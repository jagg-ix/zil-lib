import Zil.Core.Program
import ZilLib.Model
import ZilLib.SMT.Run
import ZilLib.SMT.Check
import ZilLib.SMT.Evidence
import ZilLib.Lower.Equivalence
import ZilLib.Lower.Replay
import ZilLib.Repair.Hints

/-!
# CLI Policy Equivalence Commands (APL-40)

Checks semantic equivalence between two ZIL policy models over all input fact graphs
within a finite domain bound:
  `zilLib equiv <modelA.zc> <modelB.zc> [options]`
-/

namespace ZilLib.CLI.EquivCommands

open Zil
open ZilLib.SMT
open ZilLib.Lower
open ZilLib.Lower.Equivalence
open ZilLib.Lower.Replay

structure ParsedArgs where
  positional : Array String := #[]
  options : Array (String × String) := #[]
  flags : Array String := #[]
  deriving Inhabited

def parseArgs (args : List String) : Except String ParsedArgs := do
  let mut p := #[]
  let mut opts := #[]
  let mut flgs := #[]
  let mut rest := args
  while !rest.isEmpty do
    let head := rest.head!
    rest := rest.tail!
    if head.startsWith "--" then
      if head.contains '=' then
        let parts := head.splitOn "="
        opts := opts.push (parts[0]!, "=".intercalate parts.tail!)
      else if !rest.isEmpty && !rest.head!.startsWith "-" then
        opts := opts.push (head, rest.head!)
        rest := rest.tail!
      else
        flgs := flgs.push head
    else
      p := p.push head
  return { positional := p, options := opts, flags := flgs }

def getOption (p : ParsedArgs) (key : String) : Option String :=
  p.options.find? (·.1 == key) |>.map (·.2)

def hasFlag (p : ParsedArgs) (flag : String) : Bool :=
  p.flags.contains flag

/-- Write evidence file if requested. -/
def writeEvidence (path : String) (res : SmtResult) : IO Unit := do
  match ZilLib.SMT.Evidence.ofResult res with
  | .ok json =>
      match Zil.Json.canonical json with
      | .ok canon => IO.FS.writeFile path (Zil.Json.write canon ++ "\n")
      | .error e => IO.eprintln s!"evidence canonicalization failed: {e}"
  | .error e => IO.eprintln s!"evidence creation failed: {e}"

def usage : String :=
  "Usage: zilLib equiv <modelA.zc> <modelB.zc> [options]\n\n" ++
  "Options:\n" ++
  "  --bound N, -n N   Domain size bound (default 3)\n" ++
  "  --length N        Maximum unrolling step bound (default 5)\n" ++
  "  --target REL      Target relation to compare (default: all shared derived relations)\n" ++
  "  --solver SOLVER   SMT solver executable name (default 'z3')\n" ++
  "  --timeout SEC     Solver timeout in seconds (default 30)\n" ++
  "  --evidence FILE   Path to emit ZIL-EVIDENCE/1 JSON envelope\n" ++
  "  --repair, -r      Display rule repair suggestions for identified divergences (APL-46)\n" ++
  "  --help, -h        Display this help message"

def run (args : List String) : IO UInt32 := do
  let parsed ← match parseArgs args with
    | .ok p => pure p
    | .error err =>
        IO.eprintln s!"equiv: argument error: {err}"
        return 2

  if hasFlag parsed "--help" || hasFlag parsed "-h" then
    IO.println usage
    return 0

  if parsed.positional.size < 2 then
    IO.eprintln "equiv: missing required arguments <modelA.zc> <modelB.zc>"
    IO.eprintln usage
    return 2

  let fileA := parsed.positional[0]!
  let fileB := parsed.positional[1]!

  let pA ← match ← (ZilLib.loadProgramWith ["libsets/check-vocab"] fileA).toBaseIO with
    | .ok program => pure program
    | .error err =>
        IO.eprintln s!"equiv: error loading {fileA}: {err}"
        return 2

  let pB ← match ← (ZilLib.loadProgramWith ["libsets/check-vocab"] fileB).toBaseIO with
    | .ok program => pure program
    | .error err =>
        IO.eprintln s!"equiv: error loading {fileB}: {err}"
        return 2

  let bound := ((getOption parsed "--bound").orElse (fun () => getOption parsed "-n") >>= String.toNat?).getD 3
  let targetRels := match getOption parsed "--target" with
    | some t => t.splitOn "," |>.map (fun s => s.trimAscii.toString)
    | none => []

  let (domain, tsMod, targets) ← match lowerEquivalenceModule pA pB bound targetRels with
    | .ok res => pure res
    | .error err =>
        IO.eprintln s!"equiv: lowering failed: {err}"
        return 2

  let length := ((getOption parsed "--length").orElse (fun () => getOption parsed "--depth") >>= String.toNat?).getD 5
  let timeoutSec := (getOption parsed "--timeout" >>= String.toNat?).getD 30
  let timeoutMs := timeoutSec * 1000
  let solverName := getOption parsed "--solver" |>.getD "z3"

  let tool ← match ← locateInEnvironment solverName with
    | .found t => pure t
    | .missing name =>
        IO.eprintln s!"equiv: solver '{name}' not found on PATH"
        return 3
    | .broken path detail =>
        IO.eprintln s!"equiv: solver '{path}' broken: {detail}"
        return 3

  let invName := tsMod.invariants.head!.1
  let res ← checkBMC tsMod invName length tool timeoutMs

  if let some evPath := getOption parsed "--evidence" then
    writeEvidence evPath res

  match res.verdict with
  | .noViolationWithinBound b =>
      let targetsStr := String.intercalate ", " (targets.map (·.name))
      IO.println s!"zilLib equiv: models are equivalent within bound {bound} (depth {b}, target(s): {targetsStr})"
      return 0

  | .violationFound depth trace =>
      IO.println s!"zilLib equiv: equivalence violation found at depth {depth}"
      if !trace.isEmpty then do
        let s0 := trace.toList.head!
        let baseFacts := extractBaseFacts domain tsMod s0
        IO.println s!"Counterexample base graph ({baseFacts.size} fact(s)):"
        for (rel, sub, obj) in baseFacts do
          IO.println s!"  {rel}({sub}, {obj})"

        let terminalState := trace.back?.getD s0
        let diffs := findDivergence domain tsMod terminalState targets
        IO.println s!"Divergence in target relation(s):"
        for d in diffs do
          IO.println s!"  {d.relation}({d.subject}, {d.object}): Model A = {d.valA}, Model B = {d.valB}"

        -- Lean transition replay validation
        let replayReport := replayAndCertify domain tsMod trace invName
        if replayReport.valid then
          IO.println "confirmed and replayed by Lean reference engine"
        else
          IO.println s!"warning: replay verification: {replayReport.detail}"

        -- Rule repair hints (APL-46)
        if hasFlag parsed "--repair" || hasFlag parsed "-r" then
          IO.println "\n--- Rule Repair Hints (APL-46) ---"
          let mut hintsCount := 0
          for d in diffs.toList.take 3 do
            let report := ZilLib.Repair.synthesizeRepairHints pA pB domain tsMod terminalState d
            IO.print (ZilLib.Repair.renderRepairReport report)
            hintsCount := hintsCount + report.candidatePatches.length
          if hintsCount == 0 then
            IO.println "Note: Repair hints are suggestions only and never edit files."
      return 1

  | .inconclusive reason =>
      IO.eprintln s!"zilLib equiv: inconclusive ({reason})"
      return 4

  | .rejected reason =>
      IO.eprintln s!"zilLib equiv: rejected ({reason})"
      return 2

  | .unavailable reason =>
      IO.eprintln s!"zilLib equiv: tool unavailable ({reason})"
      return 3

  | _ =>
      return 1

end ZilLib.CLI.EquivCommands
