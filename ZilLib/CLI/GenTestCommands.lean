import Zil.Core.Program
import ZilLib.Model
import ZilLib.SMT.Run
import ZilLib.GenTests.Generate

/-!
# CLI Test Generation Commands (APL-42)

Generates concrete Lean tests by negating rule/operation reachability goals,
querying SMT solvers for witness graphs, and calculating rule/operation coverage:
  `zilLib gentests <model.zc> [options]`
-/

namespace ZilLib.CLI.GenTestCommands

open Zil
open ZilLib.SMT
open ZilLib.GenTests

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

def usage : String :=
  "Usage: zilLib gentests <model.zc> [options]\n\n" ++
  "Options:\n" ++
  "  --bound N, -n N   Domain size bound for witness search (default 3)\n" ++
  "  --depth N         Maximum unrolling step bound (default 4)\n" ++
  "  --out PATH, -o    Path to write generated Lean test suite (default stdout/optional)\n" ++
  "  --solver SOLVER   SMT solver executable name (default 'z3')\n" ++
  "  --timeout SEC     Solver timeout in seconds (default 30)\n" ++
  "  --help, -h        Display this help message"

def run (args : List String) : IO UInt32 := do
  let parsed ← match parseArgs args with
    | .ok p => pure p
    | .error err =>
        IO.eprintln s!"gentests: argument error: {err}"
        return 2

  if hasFlag parsed "--help" || hasFlag parsed "-h" then
    IO.println usage
    return 0

  if parsed.positional.isEmpty then
    IO.eprintln "gentests: missing required argument <model.zc>"
    IO.eprintln usage
    return 2

  let modelFile := parsed.positional[0]!
  let p ← match ← (ZilLib.loadProgramWith ["libsets/check-vocab"] modelFile).toBaseIO with
    | .ok program => pure program
    | .error err =>
        IO.eprintln s!"gentests: error loading {modelFile}: {err}"
        return 2

  let bound := ((getOption parsed "--bound").orElse (fun () => getOption parsed "-n") >>= String.toNat?).getD 3
  let depth := (getOption parsed "--depth" >>= String.toNat?).getD 4
  let timeoutSec := (getOption parsed "--timeout" >>= String.toNat?).getD 30
  let timeoutMs := timeoutSec * 1000
  let solverName := getOption parsed "--solver" |>.getD "z3"

  let tool ← match ← locateInEnvironment solverName with
    | .found t => pure t
    | .missing name =>
        IO.eprintln s!"gentests: solver '{name}' not found on PATH"
        return 3
    | .broken path detail =>
        IO.eprintln s!"gentests: solver '{path}' broken: {detail}"
        return 3

  let report ← generateCoverage p tool bound depth timeoutMs

  let outOpt := getOption parsed "--out" |>.orElse (fun () => getOption parsed "-o")
  if let some outPath := outOpt then
    let testCode := renderLeanTestSuite report modelFile
    -- Ensure parent dir exists
    let parts := outPath.splitOn "/"
    if parts.length > 1 then
      let dir := "/".intercalate parts.dropLast
      try IO.FS.createDirAll dir catch _ => pure ()
    IO.FS.writeFile outPath testCode

  let summary := renderCoverageSummary report modelFile outOpt
  IO.println summary

  return 0

end ZilLib.CLI.GenTestCommands
