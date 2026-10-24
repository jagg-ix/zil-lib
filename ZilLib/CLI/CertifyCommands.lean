import ZilLib.Certify
import ZilLib.Certify.Verified
import ZilLib.Model

/-!
# `zilLib certify`

    zilLib certify MODEL.zc [TRACE.txt] [--lib PATH]... [--fuel N] [--limit N] [--verified]

Checks that the facts of a derivation certificate are exactly the facts the model entails. Without `TRACE.txt` the certificate is the
core's own provenance trace of the model (the engine checked against an independent checker); with it, the certificate is a
`ZIL-PROVENANCE/1` report, as `bin/zil trace` prints it, which may come from anywhere and is not trusted. `--fuel` is the number of
rounds the engine may use per stratum (by default `Zil.Engine.defaultFuel`; the engine fails if it needs more) and `--limit` the number
of problems printed.

A model that uses macros from a library is read with that library: `--lib PATH` prepends the `.zc` files of a directory (sorted by name,
as the core's `--lib DIR` reads them) or one `.zc` file, and may be repeated, in order. Without `--lib` the model is read as it is
and has to define its macros itself. The certificate is then that of the expanded program, which is what the engine runs.

`--verified` also gives the certificate to the checker of the core that has a soundness theorem (`Zil.Datalog.checkCertificate`), after
translating the program and the certificate into the Lean-embedded Datalog (`ZilLib.Certify.Verified`). That checker is a plain list
implementation: use it on programs of some hundreds of facts. If the two checkers disagree, that is reported and the exit status is 1.

Exit codes: 0 the certificate passes both checks, 1 it does not, 2 the model or the certificate cannot be read (or, with `--verified`,
cannot be translated).
-/

namespace ZilLib.CLI.CertifyCommands

open ZilLib.Certify

def usage : String := "zilLib certify MODEL.zc [TRACE.txt] [--lib PATH]... [--fuel N] [--limit N] [--verified]"

private def number? (name : String) (args : List String) : Except String (Option Nat) :=
  match args.dropWhile (· != name) with
  | _ :: value :: _ => match value.toNat? with
      | some number => pure (some number)
      | none => throw s!"{name} needs a number, not {value}"
  | [_] => throw s!"{name} needs a value"
  | [] => pure none

/-- The value of every occurrence of the option `name`, in order. -/
private def values (name : String) : List String → Except String (List String)
  | [] => pure []
  | argument :: rest =>
      if argument == name then
        match rest with
        | value :: more => do pure (value :: (← values name more))
        | [] => throw s!"{name} needs a value"
      else values name rest

/-- The positional arguments: everything that is not an option or the value of one. -/
private def positional : List String → List String
  | [] => []
  | "--fuel" :: _ :: rest | "--limit" :: _ :: rest | "--lib" :: _ :: rest => positional rest
  | argument :: rest => if argument.startsWith "--" then positional rest else argument :: positional rest

def run (args : List String) : IO UInt32 := do
  let (fuel, limit) ← match number? "--fuel" args, number? "--limit" args with
    | .ok fuel, .ok limit => pure (fuel.getD Zil.Engine.defaultFuel, limit.getD 20)
    | .error problem, _ | _, .error problem => IO.eprintln s!"{problem}\n{usage}"; return 2
  let libraries ← match values "--lib" args with
    | .ok paths => pure paths
    | .error problem => IO.eprintln s!"{problem}\n{usage}"; return 2
  let (model, traceFile) ← match positional args with
    | [model] => pure (model, none)
    | [model, trace] => pure (model, some trace)
    | _ => IO.eprintln usage; return 2
  let program ← match ← (ZilLib.loadProgramWith libraries model).toBaseIO with
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
  let mut proved := false
  if args.contains "--verified" then
    match ZilLib.Certify.Verified.check program.facts program.allRules certificate with
    | .error problem => IO.eprintln s!"{model}: cannot translate for the proved checker: {problem}"; return 2
    | .ok accepted =>
        IO.println s!"proved checker (Zil.Datalog.checkCertificate, theorem checkCertificate_sound): {if accepted then "accepted" else "refused"}"
        if accepted != report.certified then
          IO.println "the two checkers disagree; one of them is wrong, and the certificate is not certified"
          return 1
        proved := accepted
  if report.certified then
    IO.println "certified: every fact is justified, and no rule derives a fact that is missing, so the facts are exactly those the program entails."
    if proved then
      IO.println "The second checker has a soundness theorem in Lean (docs/certifying-datalog.md, CERT-10); the translation to its representation is trusted."
    else
      IO.println "This is the result of a checker that is tested but not yet verified in Lean (docs/certifying-datalog.md, CERT-10)."
    return 0
  IO.println s!"NOT certified: {report.problemCount} problem(s){if report.problemCount > report.problems.size then s!", the first {report.problems.size} shown" else ""}"
  for problem in report.problems do
    let where_ := match problem.node with | some node => s!" (fact {node})" | none => ""
    IO.println s!"  [{problem.kind}]{where_} {problem.detail}"
  return 1

end ZilLib.CLI.CertifyCommands
