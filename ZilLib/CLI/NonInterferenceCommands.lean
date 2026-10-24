import Zil.Core.Program
import ZilLib.Model
import ZilLib.SMT.Run
import ZilLib.SMT.Check
import ZilLib.SMT.Evidence
import ZilLib.Lower.Operations
import ZilLib.Operation.AST
import ZilLib.Operation.Extract

/-!
# CLI Non-Interference Checking Commands (APL-33)

Executes 2-safety hyperproperty checking for non-interference:
verifies whether secret/private relations can leak into public projections across operational steps.
-/

namespace ZilLib.CLI.NonInterferenceCommands

open Zil
open ZilLib.SMT
open ZilLib.Lower
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
  "Usage: zilLib noninterference <file> [options]\n\n" ++
  "Options:\n" ++
  "  --length N       Maximum step depth bound (default 5)\n" ++
  "  --solver SOLVER  SMT solver executable name (default 'z3')\n" ++
  "  --timeout SEC    Solver timeout in seconds (default 30)\n" ++
  "  --evidence FILE  Path to emit ZIL-EVIDENCE/1 JSON envelope\n" ++
  "  --help, -h       Display this help message"

def run (args : List String) : IO UInt32 := do
  let parsed ← match parseArgs args with
    | .ok p => pure p
    | .error err =>
        IO.eprintln s!"noninterference: argument error: {err}"
        return 2

  if hasFlag parsed "--help" || hasFlag parsed "-h" then
    IO.println usage
    return 0

  if parsed.positional.isEmpty then
    IO.eprintln "noninterference: missing required argument <file>"
    IO.eprintln usage
    return 2

  let file := parsed.positional[0]!
  let p ← match ← (ZilLib.loadProgramWith ["libsets/check-vocab"] file).toBaseIO with
    | .ok program => pure program
    | .error err =>
        IO.eprintln s!"noninterference: {err}"
        return 2

  -- Extract declared public relations from CHECK_PUBLIC facts
  let pubFacts := p.facts.filter fun f =>
    cleanName (toString f.relation) == "relation" &&
    (nodeNameOfTerm f.subject).any (·.contains "pub_")

  let publicRelations := pubFacts.filterMap (fun f => nodeNameOfTerm f.object |>.map cleanName) |>.toList
  if publicRelations.isEmpty then
    IO.eprintln "noninterference: no CHECK_PUBLIC declarations found in model"
    return 2

  let ops := extractOperations p
  let domain := operationsDomain p ops
  let tsMod := lowerNonInterferenceModule p domain ops publicRelations

  let length := ((getOption parsed "--length").orElse (fun () => getOption parsed "--depth") >>= String.toNat?).getD 5
  let timeoutSec := (getOption parsed "--timeout" >>= String.toNat?).getD 30
  let timeoutMs := timeoutSec * 1000
  let solverName := getOption parsed "--solver" |>.getD "z3"

  let tool ← match ← locateInEnvironment solverName with
    | .found t => pure t
    | .missing name =>
        IO.eprintln s!"noninterference: solver '{name}' not found on PATH"
        return 3
    | .broken path detail =>
        IO.eprintln s!"noninterference: solver '{path}' broken: {detail}"
        return 3

  -- Execute BMC 2-safety check on 2-copy product
  let res ← checkBMC tsMod "public_non_interference" length tool timeoutMs

  if let some evPath := getOption parsed "--evidence" then
    writeEvidence evPath res

  match res.verdict with
  | .noViolationWithinBound bound =>
      IO.println s!"zilLib noninterference: non-interference holds within bound {bound} (isolated policy, zero information leak)"
      return 0

  | .violationFound depth _ =>
      IO.println s!"zilLib noninterference: information leak found at depth {depth} (policy violates non-interference)"
      return 1

  | .inconclusive reason =>
      IO.eprintln s!"zilLib noninterference: inconclusive ({reason})"
      return 4

  | .rejected reason =>
      IO.eprintln s!"zilLib noninterference: rejected ({reason})"
      return 2

  | .unavailable reason =>
      IO.eprintln s!"zilLib noninterference: tool unavailable ({reason})"
      return 3

  | _ =>
      return 1

end ZilLib.CLI.NonInterferenceCommands
