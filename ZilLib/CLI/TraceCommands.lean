import Zil.Core.Program
import ZilLib.Model
import ZilLib.SMT.Run
import ZilLib.SMT.Check
import ZilLib.SMT.Evidence
import ZilLib.Lower.Replay
import ZilLib.Lower.Operations
import ZilLib.Operation.AST
import ZilLib.Operation.Extract
import ZilLib.Operation.Executor

/-!
# CLI Trace and Temporal Governance Commands (APL-32)

Executes bounded trace checks over administrative operations:
reachability, separation of duty, and lockout verification with Lean replay.
-/

namespace ZilLib.CLI.TraceCommands

open Zil
open ZilLib.SMT
open ZilLib.Lower
open ZilLib.Lower.Replay
open ZilLib.Lower.Operations
open ZilLib.Operation

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
  "Usage: zilLib trace <file> [options]\n\n" ++
  "Options:\n" ++
  "  --length N       Maximum trace step bound (default 10)\n" ++
  "  --inv QUERY      Target invariant query to verify\n" ++
  "  --solver SOLVER  SMT solver executable name (default 'z3')\n" ++
  "  --timeout SEC    Solver timeout in seconds (default 30)\n" ++
  "  --evidence FILE  Path to emit ZIL-EVIDENCE/1 JSON envelope\n" ++
  "  --help, -h       Display this help message"

def run (args : List String) : IO UInt32 := do
  let parsed ← match parseArgs args with
    | .ok p => pure p
    | .error err =>
        IO.eprintln s!"trace: argument error: {err}"
        return 2

  if hasFlag parsed "--help" || hasFlag parsed "-h" then
    IO.println usage
    return 0

  if parsed.positional.isEmpty then
    IO.eprintln "trace: missing required argument <file>"
    IO.eprintln usage
    return 2

  let file := parsed.positional[0]!
  let p ← match ← (ZilLib.loadProgramWith ["libsets/check-vocab"] file).toBaseIO with
    | .ok program => pure program
    | .error err =>
        IO.eprintln s!"trace: {err}"
        return 2

  let invNameOpt := getOption parsed "--inv"
  let (tsMod, domain, ops) ← match lowerOperationsModule p #[] invNameOpt with
    | .ok res => pure res
    | .error err =>
        IO.eprintln s!"trace: lowering failed: {err}"
        return 2

  let targetInvName ← match invNameOpt with
    | some name => pure name
    | none =>
        match tsMod.invariants.head? with
        | some (name, _) => pure name
        | none =>
            IO.eprintln "trace: no invariant specified and none found in program"
            return 2

  let length := ((getOption parsed "--length").orElse (fun () => getOption parsed "--depth") >>= String.toNat?).getD 10
  let timeoutSec := (getOption parsed "--timeout" >>= String.toNat?).getD 30
  let timeoutMs := timeoutSec * 1000
  let solverName := getOption parsed "--solver" |>.getD "z3"

  let tool ← match ← locateInEnvironment solverName with
    | .found t => pure t
    | .missing name =>
        IO.eprintln s!"trace: solver '{name}' not found on PATH"
        return 3
    | .broken path detail =>
        IO.eprintln s!"trace: solver '{path}' broken: {detail}"
        return 3

  -- Execute BMC check on operations transition system
  let res ← checkBMC tsMod targetInvName length tool timeoutMs

  if let some evPath := getOption parsed "--evidence" then
    writeEvidence evPath res

  match res.verdict with
  | .noViolationWithinBound bound =>
      IO.println s!"zilLib trace: no violation within bound {bound} (policy holds)"
      return 0

  | .violationFound depth trace =>
      IO.println s!"zilLib trace: violation found at depth {depth}"
      let opTrace := reconstructOpTrace p domain tsMod ops trace
      if !opTrace.isEmpty then
        IO.println s!"Operation trace ({opTrace.length} step(s)):"
        for inv in opTrace do
          IO.println s!"  step: {inv.opName} {repr inv.bindings}"

      -- Replay against Lean reference executor (APL-31 / APL-22)
      let execRes := executeTrace p ops p.facts opTrace
      let replay := replayAndCertify domain tsMod trace targetInvName
      match execRes with
      | .ok _ =>
          if replay.valid then
            IO.println "trace confirmed and replayed by Lean reference executor"
            return 1
          else
            IO.println s!"trace execution passed but state replay mismatch: {replay.detail}"
            return 1
      | .error err =>
          IO.println s!"trace replayed by executor: execution failed: {err}"
          return 1

  | .inconclusive reason =>
      IO.eprintln s!"zilLib trace: inconclusive ({reason})"
      return 4

  | .inductiveProved step =>
      IO.println s!"zilLib trace: inductive proved at step {step}"
      return 0

  | .nonInductive step _ =>
      IO.println s!"zilLib trace: non-inductive at step {step}"
      return 1

  | .rejected reason =>
      IO.eprintln s!"zilLib trace: rejected ({reason})"
      return 2

  | .unavailable reason =>
      IO.eprintln s!"zilLib trace: tool unavailable ({reason})"
      return 3

end ZilLib.CLI.TraceCommands
