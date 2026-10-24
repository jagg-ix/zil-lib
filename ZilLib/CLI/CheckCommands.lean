import Zil.Core.Program
import ZilLib.Model
import ZilLib.Certify.Check
import ZilLib.TransitionSystem
import ZilLib.SMT
import ZilLib.SMT.Evidence
import ZilLib.Lower
import ZilLib.CLI.SMTCommands

/-!
# `zilLib check` and `typecheck` Command Line Interface (APL-23)

    zilLib typecheck FILE
    zilLib check FILE [--inv QUERY] [--length N] [--timeout SECONDS] [--evidence FILE] [--solver NAME]

Exit codes:
- 0: no violation within bound, or typecheck succeeded.
- 1: violation found and confirmed by Lean reference replay.
- 2: rejected, unsafe rule/query, unknown invariant, or solver model failed Lean replay.
- 3: solver tool unavailable on PATH.
- 4: inconclusive (solver timeout or unknown).
-/

namespace ZilLib.CLI.CheckCommands

open Zil
open ZilLib.TransitionSystem
open ZilLib.SMT
open ZilLib.Lower
open ZilLib.Lower.Replay
open ZilLib.CLI.SMTCommands

def usage : String :=
  "zilLib typecheck FILE\n" ++
  "zilLib check FILE [--inv QUERY] [--length N] [--timeout SECONDS] [--evidence FILE] [--solver NAME]"

/-- Run `zilLib typecheck FILE`. -/
def runTypecheck (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "missing FILE argument"
    IO.eprintln usage
    return 2

  let file := args[0]!
  let p ← match ← (ZilLib.loadProgram file).toBaseIO with
    | .ok program => pure program
    | .error error =>
        IO.eprintln s!"typecheck: {error}"
        return 2

  -- 1. Structural validity
  unless p.valid do
    IO.eprintln "typecheck: program failed structural validation"
    return 2

  -- 2. Rule safety
  for r in p.allRules do
    unless r.safe do
      IO.eprintln s!"typecheck: unsafe rule '{r.name}': head or negative variables not bound positively"
      return 2

  -- 3. Stratification
  match ZilLib.Certify.stratify p.allRules with
  | .ok strata =>
      let numStrata := strata.foldl (init := 0) fun m s => max m s.2
      IO.println s!"typecheck: ok ({p.facts.size} facts, {p.allRules.size} rules across {numStrata + 1} strata, {p.queries.size} queries)"
      return 0
  | .error err =>
      IO.eprintln s!"typecheck: stratification failed: {err}"
      return 2

/-- Run `zilLib check FILE ...`. -/
def runCheck (args : List String) : IO UInt32 := do
  let valued := ["--inv", "--length", "--timeout", "--evidence", "--solver"]
  let flags := ["--ground-only"]
  let parsed ← match parseArgs args valued flags with
    | .ok p => pure p
    | .error err =>
        IO.eprintln err
        IO.eprintln usage
        return 2

  if parsed.positional.isEmpty then
    IO.eprintln "missing FILE argument"
    IO.eprintln usage
    return 2

  let file := parsed.positional[0]!
  let p ← match ← (ZilLib.loadProgram file).toBaseIO with
    | .ok program => pure program
    | .error error =>
        IO.eprintln s!"check: {error}"
        return 2

  -- Determine invariant query name
  let invName ← match getOption parsed "--inv" with
    | some inv => pure inv
    | none =>
        match p.queries[0]? with
        | some q => pure (toString q.name)
        | none =>
            IO.eprintln "missing required option: --inv <query> (program has no queries)"
            return 2

  -- Lower program to TSModule
  let (domain, tsMod) ← match lowerProgram p (some invName) with
    | .ok res => pure res
    | .error err =>
        IO.eprintln s!"check: lowering failed: {err}"
        return 2

  let length := (getOption parsed "--length" >>= String.toNat?).getD 10
  let timeoutSec := (getOption parsed "--timeout" >>= String.toNat?).getD 30
  let timeoutMs := timeoutSec * 1000
  let solverName := getOption parsed "--solver" |>.getD "z3"

  let tool ← match ← locateInEnvironment solverName with
    | .found t => pure t
    | .missing name =>
        IO.eprintln s!"solver '{name}' not found on PATH"
        return 3
    | .broken path detail =>
        IO.eprintln s!"solver '{path}' broken: {detail}"
        return 3

  -- Execute BMC via TS-03 SMT backend
  let res ← checkBMC tsMod invName length tool timeoutMs

  if let some evPath := getOption parsed "--evidence" then
    writeEvidence evPath res

  match res.verdict with
  | .noViolationWithinBound bound =>
      IO.println s!"zilLib check: no violation within bound {bound}"
      return 0

  | .violationFound depth trace =>
      -- Replay and certify against Lean reference (APL-22, CERT-12)
      let replay := replayAndCertify domain tsMod trace invName
      if replay.valid then
        IO.println s!"zilLib check: violation found at depth {depth} (replayed and confirmed by Lean reference engine)"
        let mut step := 0
        for stepFacts in replay.factsPerStep do
          IO.println s!"State {step} ({stepFacts.size} facts):"
          for f in stepFacts do
            IO.println s!"  {ZilLib.Certify.render f}"
          step := step + 1
        return 1
      else
        IO.eprintln s!"zilLib check: candidate solver trace rejected by Lean reference replay: {replay.detail}"
        return 2

  | .inconclusive reason =>
      IO.eprintln s!"zilLib check: inconclusive: {reason}"
      return 4

  | .unavailable reason =>
      IO.eprintln s!"zilLib check: unavailable: {reason}"
      return 3

  | .rejected reason =>
      IO.eprintln s!"zilLib check: rejected: {reason}"
      return 2

  | _ =>
      return 2

end ZilLib.CLI.CheckCommands
