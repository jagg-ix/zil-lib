import ZilLib.Certify
import ZilLib.Model

/-!
# `zilLib certify`

    zilLib certify MODEL.zc [TRACE.txt] [--fuel N] [--limit N]

Checks that the facts of a derivation certificate are exactly the facts the model entails. Without `TRACE.txt` the certificate is the
core's own provenance trace of the model (the engine checked against an independent checker); with it, the certificate is a
`ZIL-PROVENANCE/1` report, as `bin/zil trace` prints it, which may come from anywhere and is not trusted. `--fuel` is the number of
rounds the engine may use per stratum (by default `Zil.Engine.defaultFuel`; the engine fails if it needs more) and `--limit` the number
of problems printed.

The model is read as it is: expand the macros first (`zil expand ... --lib DIR`), as for `explain-query`.

Exit codes: 0 the certificate passes both checks, 1 it does not, 2 the model or the certificate cannot be read.
-/

namespace ZilLib.CLI.CertifyCommands

open ZilLib.Certify

def usage : String := "zilLib certify MODEL.zc [TRACE.txt] [--fuel N] [--limit N]"

private def number? (name : String) (args : List String) : Except String (Option Nat) :=
  match args.dropWhile (· != name) with
  | _ :: value :: _ => match value.toNat? with
      | some number => pure (some number)
      | none => throw s!"{name} needs a number, not {value}"
  | [_] => throw s!"{name} needs a value"
  | [] => pure none

/-- The positional arguments: everything that is not an option or the value of one. -/
private def positional : List String → List String
  | [] => []
  | "--fuel" :: _ :: rest | "--limit" :: _ :: rest => positional rest
  | argument :: rest => if argument.startsWith "--" then positional rest else argument :: positional rest

def run (args : List String) : IO UInt32 := do
  let (fuel, limit) ← match number? "--fuel" args, number? "--limit" args with
    | .ok fuel, .ok limit => pure (fuel.getD Zil.Engine.defaultFuel, limit.getD 20)
    | .error problem, _ | _, .error problem => IO.eprintln s!"{problem}\n{usage}"; return 2
  let (model, traceFile) ← match positional args with
    | [model] => pure (model, none)
    | [model, trace] => pure (model, some trace)
    | _ => IO.eprintln usage; return 2
  let program ← match ← (ZilLib.loadProgram model).toBaseIO with
    | .ok program => pure program
    | .error error => IO.eprintln (toString error); return 2
  unless program.valid do
    IO.eprintln s!"{model}: the program is not valid (an unsafe rule or query, or an invalid declaration)"
    return 2
  let certificate ← match traceFile with
    | some file =>
        match ← (IO.FS.readFile file).toBaseIO with
        | .error error => IO.eprintln (toString error); return 2
        | .ok text =>
            match parseProvenance text with
            | .ok certificate => pure certificate
            | .error problem => IO.eprintln s!"{file}: {problem}"; return 2
    | none =>
        match Zil.Engine.Provenance.traceProgram program fuel with
        | .ok trace => pure (Certificate.ofTrace trace)
        | .error problem => IO.eprintln s!"{model}: {problem}"; return 2
  let report := check program.facts program.allRules certificate limit
  IO.println s!"certificate: {report.facts} facts, {report.database} from the database and {report.derived} derived"
  IO.println s!"closure check: {report.instances} rule instances examined"
  if report.certified then
    IO.println "certified: every fact is justified, and no rule derives a fact that is missing, so the facts are exactly those the program entails."
    IO.println "This is the result of a checker that is tested but not yet verified in Lean (docs/certifying-datalog.md, CERT-10)."
    return 0
  IO.println s!"NOT certified: {report.problemCount} problem(s){if report.problemCount > report.problems.size then s!", the first {report.problems.size} shown" else ""}"
  for problem in report.problems do
    let where_ := match problem.node with | some node => s!" (fact {node})" | none => ""
    IO.println s!"  [{problem.kind}]{where_} {problem.detail}"
  return 1

end ZilLib.CLI.CertifyCommands
