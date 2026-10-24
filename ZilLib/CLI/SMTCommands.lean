import ZilLib.TransitionSystem
import ZilLib.SMT
import ZilLib.SMT.Evidence

/-!
# `zilLib smt` Command Line Interface (TS-03)

    zilLib smt version [--solver NAME]
    zilLib smt check MODULE --inv INV [--length N] [--timeout SECONDS] [--evidence FILE] [--solver NAME]
    zilLib smt induct MODULE --inv INV [--step K] [--timeout SECONDS] [--evidence FILE] [--solver NAME]

Exit codes:
- 0: no violation within bound, or invariant proved inductive.
- 1: violation confirmed by Lean reference replay, or invariant is not inductive.
- 2: rejected, unknown module/invariant, or solver model failed Lean replay.
- 3: solver tool unavailable on PATH.
- 4: inconclusive (solver timeout or unknown).
-/

namespace ZilLib.CLI.SMTCommands

open ZilLib.TransitionSystem
open ZilLib.SMT
open Zil.Json

def usage : String :=
  "zilLib smt version [--solver NAME]\n" ++
  "zilLib smt check MODULE --inv INV [--length N] [--timeout SECONDS] [--evidence FILE] [--solver NAME]\n" ++
  "zilLib smt induct MODULE --inv INV [--step K] [--timeout SECONDS] [--evidence FILE] [--solver NAME]"

/-- Split command arguments into positional arguments and options. -/
structure ParsedArgs where
  positional : Array String := #[]
  options : Array (String × String) := #[]
  flags : Array String := #[]

def parseArgs (args : List String) (valued : List String) (flags : List String) : Except String ParsedArgs := do
  let mut p : ParsedArgs := {}
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | [] => pure ()
    | arg :: tail =>
        if arg.startsWith "--" then
          if flags.contains arg then
            p := { p with flags := p.flags.push arg }
            rest := tail
          else if valued.contains arg then
            match tail with
            | val :: tail' =>
                p := { p with options := p.options.push (arg, val) }
                rest := tail'
            | [] => throw s!"option '{arg}' requires a value"
          else throw s!"unknown option: '{arg}'"
        else
          p := { p with positional := p.positional.push arg }
          rest := tail
  pure p

def getOption (p : ParsedArgs) (key : String) : Option String :=
  p.options.find? (·.1 == key) |>.map (·.2)

/-- Resolve built-in or loaded module by name. -/
def resolveModule (name : String) : Except String TSModule :=
  match name.toLower with
  | "counter" => .ok counterModule
  | "counterdefective" => .ok counterDefectiveModule
  | "lockstep" => .ok lockStepModule
  | _ => .error s!"unknown module '{name}'; available: Counter, CounterDefective, LockStep"

/-- Print a trace state by state. -/
def printTrace (m : TSModule) (trace : Array TSState) : IO Unit := do
  let mut idx := 0
  for s in trace do
    IO.println s!"State {idx}"
    idx := idx + 1
    for v in m.variables do
      let valStr := match TSState.getVar m s v.name with
        | some (.int n) => toString n
        | some (.bool b) => if b then "TRUE" else "FALSE"
        | some (.enumVal _ val) => val
        | none => "<none>"
      IO.println s!"  {v.name} = {valStr}"

/-- Write evidence file if requested. -/
def writeEvidence (path : String) (res : SmtResult) : IO Unit := do
  match ZilLib.SMT.Evidence.ofResult res with
  | .ok json =>
      match Zil.Json.canonical json with
      | .ok canon => IO.FS.writeFile path (Zil.Json.write canon ++ "\n")
      | .error e => IO.eprintln s!"evidence canonicalization failed: {e}"
  | .error e => IO.eprintln s!"evidence creation failed: {e}"

/-- Main entry point for `zilLib smt`. -/
def run (args : List String) : IO UInt32 := do
  let valued := ["--inv", "--length", "--step", "--timeout", "--evidence", "--solver"]
  let flags := ["--no-deadlock"]
  let parsed ← match parseArgs args valued flags with
    | .ok p => pure p
    | .error err =>
        IO.eprintln err
        IO.eprintln usage
        return 2

  let cmd := parsed.positional[0]?.getD ""
  let solverName := getOption parsed "--solver" |>.getD "z3"

  match cmd with
  | "version" =>
      match ← locateInEnvironment solverName with
      | .found tool =>
          IO.println s!"{tool.name}: {tool.version}"
          return 0
      | .missing name =>
          IO.eprintln s!"solver '{name}' not found on PATH"
          return 3
      | .broken path detail =>
          IO.eprintln s!"solver at '{path}' is broken: {detail}"
          return 3

  | "check" =>
      let modName ← match parsed.positional[1]? with
        | some n => pure n
        | none =>
            IO.eprintln "missing MODULE argument"
            IO.eprintln usage
            return 2

      let m ← match resolveModule modName with
        | .ok m => pure m
        | .error err =>
            IO.eprintln err
            return 2

      let invName ← match getOption parsed "--inv" with
        | some inv => pure inv
        | none =>
            IO.eprintln "missing required option: --inv <name>"
            return 2

      let length := (getOption parsed "--length" >>= String.toNat?).getD 10
      let timeoutSec := (getOption parsed "--timeout" >>= String.toNat?).getD 30
      let timeoutMs := timeoutSec * 1000

      let tool ← match ← locateInEnvironment solverName with
        | .found t => pure t
        | .missing name =>
            IO.eprintln s!"solver '{name}' not found on PATH"
            return 3
        | .broken path detail =>
            IO.eprintln s!"solver '{path}' broken: {detail}"
            return 3

      let res ← checkBMC m invName length tool timeoutMs

      if let some evPath := getOption parsed "--evidence" then
        writeEvidence evPath res

      match res.verdict with
      | .noViolationWithinBound bound =>
          IO.println s!"zilLib smt check: no violation within bound {bound}"
          return 0
      | .violationFound depth trace =>
          IO.println s!"zilLib smt check: violation found at depth {depth}"
          printTrace m trace
          return 1
      | .rejected reason =>
          IO.eprintln s!"zilLib smt check: rejected: {reason}"
          return 2
      | .inconclusive reason =>
          IO.eprintln s!"zilLib smt check: inconclusive: {reason}"
          return 4
      | .unavailable reason =>
          IO.eprintln s!"zilLib smt check: unavailable: {reason}"
          return 3
      | _ =>
          return 2

  | "induct" =>
      let modName ← match parsed.positional[1]? with
        | some n => pure n
        | none =>
            IO.eprintln "missing MODULE argument"
            IO.eprintln usage
            return 2

      let m ← match resolveModule modName with
        | .ok m => pure m
        | .error err =>
            IO.eprintln err
            return 2

      let invName ← match getOption parsed "--inv" with
        | some inv => pure inv
        | none =>
            IO.eprintln "missing required option: --inv <name>"
            return 2

      let k := (getOption parsed "--step" >>= String.toNat?).getD 1
      let timeoutSec := (getOption parsed "--timeout" >>= String.toNat?).getD 30
      let timeoutMs := timeoutSec * 1000

      let tool ← match ← locateInEnvironment solverName with
        | .found t => pure t
        | .missing name =>
            IO.eprintln s!"solver '{name}' not found on PATH"
            return 3
        | .broken path detail =>
            IO.eprintln s!"solver '{path}' broken: {detail}"
            return 3

      let res ← checkInduct m invName k tool timeoutMs

      if let some evPath := getOption parsed "--evidence" then
        writeEvidence evPath res

      match res.verdict with
      | .inductiveProved k =>
          IO.println s!"zilLib smt induct: invariant '{invName}' is {k}-inductive"
          return 0
      | .nonInductive k trace =>
          IO.println s!"zilLib smt induct: invariant '{invName}' is not {k}-inductive"
          if !trace.isEmpty then
            printTrace m trace
          return 1
      | .violationFound depth trace =>
          IO.println s!"zilLib smt induct: base violation found at depth {depth}"
          printTrace m trace
          return 1
      | .rejected reason =>
          IO.eprintln s!"zilLib smt induct: rejected: {reason}"
          return 2
      | .inconclusive reason =>
          IO.eprintln s!"zilLib smt induct: inconclusive: {reason}"
          return 4
      | .unavailable reason =>
          IO.eprintln s!"zilLib smt induct: unavailable: {reason}"
          return 3
      | _ =>
          return 2

  | _ =>
      IO.eprintln usage
      return 2

end ZilLib.CLI.SMTCommands
