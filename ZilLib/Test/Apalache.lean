import ZilLib.Apalache
import ZilLib.CLI.ApalacheCommands
import ZilLib.Test.Harness

/-!
# Tests of the Apalache modules

Run from the repository root, because the fixtures are read from `test/fixtures/apalache/`. Most tests use the stand-in tool in
`fake-home/`, which starts no JVM, so the gate can run them with failing `java` and `apalache-mc` programs first on `PATH`. The
tests of the last group start the real tool and run only with `--with-tool`; without the tool they are skipped.
-/

namespace ZilLib.Test.Apalache

open ZilLib.Apalache Zil.Json

open ZilLib.Test

private def fixtures : System.FilePath := "test/fixtures/apalache"

private def sameJson (a b : J) : Bool :=
  match Zil.Json.canonical a, Zil.Json.canonical b with
  | .ok x, .ok y => x == y
  | _, _ => false

private def remove (result : Result) : IO Unit := do
  if let some directory := result.outDir then
    if ← directory.pathExists then IO.FS.removeDirAll directory

/-! ## Traces -/

private def traceTests (t : Tally) : IO Unit := do
  for name in ["counter.violation.itf.json", "sym.violation.itf.json"] do
    let text ← IO.FS.readFile (fixtures / name)
    match Itf.Trace.parse text, Zil.Json.parse text with
    | .ok trace, .ok json => t.expect s!"{name}: the trace written back equals the file" (sameJson trace.toJson json)
    | _, _ => t.expect s!"{name}: it can be read" false
  match Itf.Trace.parse (← IO.FS.readFile (fixtures / "counter.violation.itf.json")) with
  | .ok trace =>
      t.expect "counter trace: four states and the variable n" (trace.states.size == 4 && trace.vars == #["n"])
      t.expect "counter trace: n counts from 0 to 3"
        ((List.range 4).all fun index => trace.valueOf? index "n" == some (.int index))
      t.expect "counter trace: the text lists each state" (contains trace.render "State 3\n  n = 3\n")
  | .error problem => t.expect "counter trace: it can be read" false problem
  match Itf.Trace.parse (← IO.FS.readFile (fixtures / "sym.violation.itf.json")) with
  | .ok trace =>
      t.expect "sym trace: the constant Nodes is listed and has a value in the first state"
        (trace.params == #["Nodes"] && (trace.valueOf? 0 "Nodes").isSome)
      let text := trace.render
      t.expect "sym trace: a set of tuples of uninterpreted values" (contains text "<<\"a_OF_NODE\", \"b_OF_NODE\">>")
      t.expect "sym trace: the set of nodes" (contains text "Nodes = {\"a_OF_NODE\", \"b_OF_NODE\", \"c_OF_NODE\"}")
  | .error problem => t.expect "sym trace: it can be read" false problem
  let synthetic := "{\"#meta\":{\"format\":\"ITF\"},\"vars\":[\"r\"],\"states\":[{\"#meta\":{\"index\":0},\"r\":{\"x\":{\"#bigint\":\"123456789012345678901234567890\"},\"m\":{\"#map\":[[\"k\",true]]},\"u\":{\"#unserializable\":\"f\"}}}],\"loop\":0}"
  match Itf.Trace.parse synthetic with
  | .ok trace =>
      t.expect "a record with a big integer, a map and an unserializable value, and a loop"
        (trace.render == "State 0\n  r = [x |-> 123456789012345678901234567890, m |-> (\"k\" :> TRUE), u |-> <unserializable: f>]\nThe trace returns to state 0\n"
          && trace.loop == some 0)
  | .error problem => t.expect "a synthetic trace can be read" false problem
  let refuses (name text expected : String) : IO Unit :=
    match Itf.Trace.parse text with
    | .ok _ => t.expect name false "it was accepted"
    | .error problem => t.expect name (contains problem expected) problem
  refuses "a document that is not ITF is refused" "{\"#meta\":{\"format\":\"JSON\"},\"states\":[]}" "not an ITF trace"
  refuses "an unknown tag is refused" "{\"#meta\":{\"format\":\"ITF\"},\"vars\":[],\"states\":[{\"a\":{\"#bogus\":1}}]}" "unknown tag"
  refuses "an untagged array is refused" "{\"#meta\":{\"format\":\"ITF\"},\"vars\":[],\"states\":[{\"a\":[1,2]}]}" "not tagged"
  refuses "an integer that is not one is refused" "{\"#meta\":{\"format\":\"ITF\"},\"vars\":[],\"states\":[{\"a\":{\"#bigint\":\"x\"}}]}" "not an integer"

/-! ## The runner, against the stand-in -/

private def standIn (home : String) : IO Located :=
  locate (some (fixtures / home).toString) []

private def config (model : String) : Config :=
  { model := fixtures / "fake-models" / s!"{model}.tla", inv := #["Inv"], length := 5, timeoutMs := 20000 }

private def runnerTests (t : Tally) : IO Unit := do
  t.expect "the options become the arguments of the tool"
    ({ model := "M.tla", init := some "I", next := some "N", inv := #["A", "B"], cinit := some "C", length := 3,
       noDeadlock := true : Config }.arguments "OUT"
      == #["check", "--init=I", "--next=N", "--inv=A,B", "--cinit=C", "--length=3", "--no-deadlock", "--out-dir=OUT", "M.tla"])
  t.expect "the outcome is the word after 'The outcome is:'" (outcomeOf "x\nThe outcome is: Deadlock    I@1\ny" == some "Deadlock")
  t.expect "no outcome line, no outcome" (outcomeOf "nothing here" == none)
  t.expect "exit 12 is a violation unless the outcome says deadlock"
    (verdictOf 12 none == .violation && verdictOf 12 (some "Deadlock") == .deadlock)
  t.expect "exit 0 is a pass; ExecutionsTooShort is a pass with a shorter depth"
    (verdictOf 0 (some "NoError") == .noError && verdictOf 0 (some "ExecutionsTooShort") == .tooShort)
  t.expect "another exit code is a failure, not interpreted" (verdictOf 7 none == .failed 7 && verdictOf 255 none == .failed 255)
  match ← standIn "fake-home" with
  | .found tool => t.expect "the stand-in is found and reports its version" (tool.version == "0.0.0-fake")
  | _ => t.expect "the stand-in is found" false
  t.expect "no tool in the home and an empty search path: missing"
    (match ← locate (some "/nonexistent") [] with | .missing => true | _ => false)
  match ← standIn "broken-home" with
  | .broken _ detail => t.expect "an executable that reports no version is broken, with the reason" (contains detail "99")
  | _ => t.expect "an executable that reports no version is broken" false
  let some tool := (match ← standIn "fake-home" with | .found tool => some tool | _ => none) | return
  let verdictOfModel (model : String) (expected : Verdict) (extra : Result → Bool := fun _ => true) : IO Unit := do
    let result ← check (config model) tool
    t.expect s!"{model}: {repr expected}" (result.verdict == expected && extra result) s!"got {repr result.verdict}"
    remove result
  verdictOfModel "Passing" .noError fun result => result.outcome == some "NoError" && result.exitCode == some 0 && result.trace.isNone
  verdictOfModel "Short" .tooShort
  verdictOfModel "Violating" .violation fun result =>
    result.exitCode == some 12 && result.command.contains "--inv=Inv" && result.command.contains "--length=5"
      && (result.trace.map (·.states.size)) == some 4 && result.traceProblem.isNone
  verdictOfModel "Deadlocking" .deadlock fun result => result.trace.isSome
  verdictOfModel "Rejected" (.failed 255)
  let slow ← check { config "Slow" with timeoutMs := 400 } tool
  t.expect "a run that passes its deadline is killed and reported as timed out" (slow.verdict == .timedOut && slow.elapsedMs < 10000)
  remove slow
  let missing ← check { config "Passing" with model := fixtures / "fake-models" / "Absent.tla" } tool
  t.expect "a model that does not exist is refused before the tool runs" (match missing.verdict with | .rejected _ => true | _ => false)
  let same ← check { config "Passing" with outDir := some (fixtures / "fake-models") } tool
  t.expect "an output directory that is the model's directory is refused"
    (match same.verdict with | .rejected reason => contains reason "directory of the model" | _ => false)
  let fresh ← IO.FS.createTempDir
  let named ← check { config "Violating" with outDir := some (fresh / "out") } tool
  t.expect "a named output directory is created and used" (named.outDir == some (fresh / "out") && named.trace.isSome)
  IO.FS.removeDirAll fresh
  let first ← check (config "Passing") tool
  let second ← check (config "Passing") tool
  t.expect "every run without a named directory gets a new one" (first.outDir != second.outDir && first.outDir.isSome)
  remove first
  remove second
  t.expect "the exit codes of the command line"
    ([Verdict.noError, .tooShort, .violation, .deadlock, .failed 255, .rejected "", .unavailable "", .timedOut].map
        ZilLib.CLI.ApalacheCommands.exitCodeOf == [0, 0, 1, 1, 2, 2, 3, 4])
  let parsed := ZilLib.CLI.ApalacheCommands.parseArguments ["M.tla", "--inv", "A", "--no-deadlock"] ["--inv"] ["--no-deadlock"]
  t.expect "a command line is split into positional arguments, options and flags"
    (match parsed with
      | .ok parsed => parsed.positional == #["M.tla"] && parsed.options == #[("--inv", "A")] && parsed.flags == #["--no-deadlock"]
      | .error _ => false)
  t.expect "an unknown option and a missing value are refused"
    ((ZilLib.CLI.ApalacheCommands.parseArguments ["--bogus"] [] []).toBool == false
      && (ZilLib.CLI.ApalacheCommands.parseArguments ["--inv"] ["--inv"] []).toBool == false)

/-! ## Evidence -/

private def field (envelope : J) (name : String) : String := (envelope.getStr? name).getD ""

private def evidenceOf (config : Config) (result : Result) : IO (Option J) := do
  match ← Evidence.ofCheck config result with
  | some (.ok envelope) => pure (some envelope)
  | _ => pure none

private def evidenceTests (t : Tally) : IO Unit := do
  let some tool := (match ← standIn "fake-home" with | .found tool => some tool | _ => none) | return
  let violating := config "Violating"
  let result ← check violating tool
  match ← evidenceOf violating result with
  | none => t.expect "a violation has an envelope" false
  | some envelope =>
      t.expect "the core accepts the envelope" (match Zil.Plugin.Evidence.validate envelope with | .ok _ => true | .error _ => false)
      t.expect "authority external, assurance externally-attested, role bounded-model-checker"
        (field envelope "authority" == "external" && field envelope "assurance" == "externally-attested"
          && field envelope "role" == "bounded-model-checker")
      t.expect "the subject names the kind, the model and the invariants" (field envelope "subject" == "check:Violating.tla:Inv")
      t.expect "the payload names the verdict and states the bound"
        (contains (field envelope "payload") "violation-found" && contains (field envelope "payload") "at most 5 steps")
      t.expect "neither the output directory nor the time is part of the payload"
        (!contains (field envelope "payload") "elapsed" && !contains (field envelope "payload") (result.outDir.map toString |>.getD "?"))
      let again ← check violating tool
      let sameId := (← evidenceOf violating again).map (field · "evidence_id") == some (field envelope "evidence_id")
      t.expect "the same request gives the same evidence id, run after run" sameId
      remove again
      -- the digest of the inputs must change with each part of the request, not only the identity (the payload also names the bound)
      let inputsOf (variant : Config) : IO (Option String) := do
        let ran ← check variant tool
        let digest := (← evidenceOf variant ran).map (field · "input_sha256")
        remove ran
        pure digest
      let original := field envelope "input_sha256"
      t.expect "a different bound changes the digest of the inputs" ((← inputsOf { violating with length := 6 }) != some original)
      t.expect "a different invariant changes the digest of the inputs" ((← inputsOf { violating with inv := #["Other"] }) != some original)
      t.expect "a different constants predicate changes the digest of the inputs" ((← inputsOf { violating with cinit := some "CInit" }) != some original)
      t.expect "a different initial predicate changes the digest of the inputs" ((← inputsOf { violating with init := some "Start" }) != some original)
      t.expect "a different next-state predicate changes the digest of the inputs" ((← inputsOf { violating with next := some "Step" }) != some original)
      t.expect "the deadlock switch changes the digest of the inputs" ((← inputsOf { violating with noDeadlock := true }) != some original)
      t.expect "the same request has the same digest of the inputs" ((← inputsOf violating) == some original)
      let longerResult ← check { violating with length := 6 } tool
      t.expect "a different bound gives a different evidence id"
        ((← evidenceOf { violating with length := 6 } longerResult).map (field · "evidence_id") != some (field envelope "evidence_id"))
      remove longerResult
  remove result
  -- a changed model changes the identity: copy the model, add a line, and compare
  let scratch ← IO.FS.createTempDir
  let copy := scratch / "Violating.tla"
  IO.FS.writeFile copy ((← IO.FS.readFile (fixtures / "fake-models" / "Violating.tla")) ++ "\\* changed\n")
  let changed := { violating with model := copy }
  let changedResult ← check changed tool
  let original ← check violating tool
  t.expect "a changed model gives a different evidence id and a different digest of the inputs"
    ((← evidenceOf changed changedResult).map (field · "evidence_id") != (← evidenceOf violating original).map (field · "evidence_id")
      && (← evidenceOf changed changedResult).map (field · "input_sha256") != (← evidenceOf violating original).map (field · "input_sha256"))
  remove changedResult
  remove original
  IO.FS.removeDirAll scratch
  let slow ← check { config "Slow" with timeoutMs := 400 } tool
  match ← evidenceOf (config "Slow") slow with
  | some envelope =>
      t.expect "a timeout is recorded as inconclusive and never as a pass"
        (contains (field envelope "payload") "inconclusive-timeout" && !contains (field envelope "payload") "no-violation")
  | none => t.expect "a timeout has an envelope" false
  remove slow
  let rejected ← check (config "Rejected") tool
  t.expect "a run the tool rejects says nothing about the model and has no envelope" ((← Evidence.ofCheck (config "Rejected") rejected).isNone)
  remove rejected
  let passing ← check (config "Passing") tool
  match ← evidenceOf (config "Passing") passing with
  | some envelope => t.expect "a pass is recorded within its bound" (contains (field envelope "payload") "no-violation-within-bound")
  | none => t.expect "a pass has an envelope" false
  remove passing
  t.expect "the version in the evidence is the version of the package"
    (contains (← IO.FS.readFile "lakefile.lean") s!"version := v!\"{Evidence.version}\"")
  t.expect "EXTENDS names are read" (Evidence.extendedNames "---- MODULE A ----\nEXTENDS B, Integers\nx == 1\n" == #["B", "Integers"])
  let directory ← IO.FS.createTempDir
  IO.FS.writeFile (directory / "A.tla") "---- MODULE A ----\nEXTENDS B, Integers\n====\n"
  IO.FS.writeFile (directory / "B.tla") "---- MODULE B ----\n====\n"
  let digests ← Evidence.moduleDigests (directory / "A.tla")
  t.expect "the model and the modules it extends next to it are digested, standard modules are not" (digests.map (·.1) == #["A.tla", "B.tla"])
  IO.FS.removeDirAll directory

/-! ## Induction, against the stand-in -/

private def inductionTests (t : Tally) : IO Unit := do
  let some tool := (match ← standIn "fake-home" with | .found tool => some tool | _ => none) | return
  let induct (model : String) : Induct.Config :=
    { model := fixtures / "fake-models" / s!"{model}.tla", indInit := "IndInit", inv := #["IndInv"], timeoutMs := 20000 }
  let cases : List (String × String) := [("Inductive", "holds"), ("NotInductive", "not inductive"), ("BaseFails", "base fails")]
  for (model, label) in cases do
    let outcome ← Induct.run (induct model) tool
    let ok := match model, outcome with
      | "Inductive", .holds .. => true
      | "NotInductive", .notInductive _ step => step.trace.isSome
      | "BaseFails", .baseFails _ => true
      | _, _ => false
    t.expect s!"{model}: {label}" ok
    let verdict := outcome.verdict
    t.expect s!"{model}: the evidence names {verdict.getD "nothing"}"
      (verdict == some (match model with | "Inductive" => "inductive-at-the-constants" | "NotInductive" => "counterexample-to-induction" | _ => "base-case-violated"))
    match ← Induct.evidence (induct model) outcome with
    | some (.ok envelope) =>
        t.expect s!"{model}: the core accepts the envelope"
          ((match Zil.Plugin.Evidence.validate envelope with | .ok _ => true | .error _ => false) && field envelope "subject" == s!"induction:{model}.tla:IndInv")
    | _ => t.expect s!"{model}: the evidence exists" false
    for result in [outcome.last] do remove result
    match outcome with
    | .holds base step => remove base; remove step
    | .notInductive base step => remove base; remove step
    | _ => pure ()
  let outcome ← Induct.run { induct "Slow" with timeoutMs := 400 } tool
  t.expect "a base case that times out is inconclusive, not a pass"
    (match outcome with | .stopped "base case" result => result.verdict == .timedOut | _ => false)
  t.expect "an inconclusive run has evidence that says so" (outcome.verdict == some "inconclusive-timeout")
  t.expect "the report of a passing check says it is not a proof for other sizes"
    (contains (Induct.report (induct "Inductive") (.holds {verdict := .noError} {verdict := .noError})) "not a proof for other sizes")
  t.expect "the report of a counterexample to induction says it is a finding"
    (contains (Induct.report (induct "NotInductive") (.notInductive {verdict := .noError} {verdict := .violation})) "a finding, not a defect")
  t.expect "the base case runs at length 0 from Init, the step at length 1 from the given predicate, both without the deadlock check"
    ((induct "Inductive").base.length == 0 && (induct "Inductive").base.init == some "Init"
      && (induct "Inductive").step.length == 1 && (induct "Inductive").step.init == some "IndInit"
      && (induct "Inductive").base.noDeadlock && (induct "Inductive").step.noDeadlock)

/-! ## The real tool -/

private def realToolTests (t : Tally) : IO Unit := do
  let tool ← match ← locateInEnvironment with
    | .found tool => pure tool
    | _ =>
        IO.println "SKIP  the tests with the real tool: apalache-mc was not found in APALACHE_HOME or PATH"
        return
  IO.println s!"tool: {toolName} {tool.version} ({tool.path})"
  let model (name : String) := fixtures / s!"{name}.tla"
  let counter ← check { model := model "Counter", inv := #["Inv"], length := 5, timeoutMs := 300000 } tool
  t.expect "Counter: n < 3 is violated at the fourth state (exit 12, outcome Error)"
    (counter.verdict == .violation && counter.outcome == some "Error" && (counter.trace.map (·.states.size)) == some 4)
  match counter.trace, Itf.Trace.parse (← IO.FS.readFile (fixtures / "counter.violation.itf.json")) with
  | some written, .ok kept =>
      t.expect "Counter: the trace the tool writes now has the states of the trace kept as a fixture"
        (written.states.size == kept.states.size
          && (List.range 4).all (fun index => written.valueOf? index "n" == kept.valueOf? index "n"))
  | _, _ => t.expect "Counter: the trace can be read" false
  remove counter
  let short ← check { model := model "Counter", inv := #["Inv"], length := 2, timeoutMs := 300000 } tool
  t.expect "Counter: no violation within 2 steps" (short.verdict == .noError)
  remove short
  let sym ← check { model := model "Sym", inv := #["Anti"], cinit := some "ConstInit", length := 0, timeoutMs := 300000 } tool
  t.expect "Sym: antisymmetry fails for some graph, with the constant and a set of tuples in the trace"
    (sym.verdict == .violation && (sym.trace.map (·.params)) == some #["Nodes"])
  remove sym
  let closed ← check { model := model "Sym", inv := #["Closed"], cinit := some "ConstInit", length := 0, timeoutMs := 300000 } tool
  t.expect "Sym: a property of every graph holds" (closed.verdict == .noError)
  remove closed
  let stuck ← check { model := model "Stuck", inv := #["Inv"], length := 5, timeoutMs := 300000 } tool
  t.expect "Stuck: a state without a successor is a deadlock (exit 12, outcome Deadlock)" (stuck.verdict == .deadlock)
  remove stuck
  let ignoring ← check { model := model "Stuck", inv := #["Inv"], length := 5, noDeadlock := true, timeoutMs := 300000 } tool
  t.expect "Stuck: with --no-deadlock the run passes, with the outcome ExecutionsTooShort" (ignoring.verdict == .tooShort)
  remove ignoring
  let untyped ← check { model := model "Untyped", inv := #["Inv"], length := 3, timeoutMs := 300000 } tool
  t.expect "Untyped: a variable without a type is refused by the tool (exit 255)" (untyped.verdict == .failed 255)
  remove untyped
  let lockStep (cinit indInit invariant : String) : Induct.Config :=
    { model := model "LockStep", cinit := some cinit, indInit, inv := #[invariant], timeoutMs := 300000 }
  let weak ← Induct.run (lockStep "CInit" "WeakInit" "Bounded") tool
  match weak with
  | .notInductive _ step =>
      t.expect "LockStep: Bounded is true but not inductive; the counterexample to induction starts with b at Max"
        (step.trace.bind (·.valueOf? 0 "b") == some (.int 5))
  | _ => t.expect "LockStep: Bounded is not inductive" false
  let strong ← Induct.run (lockStep "CInit" "StrongInit" "IndInv") tool
  t.expect "LockStep: Bounded together with a = b is inductive at Max = 5" (match strong with | .holds .. => true | _ => false)
  match ← Induct.evidence (lockStep "CInit" "StrongInit" "IndInv") strong with
  | some (.ok envelope) =>
      t.expect "LockStep: the evidence says inductive at the constants, externally attested"
        (contains (field envelope "payload") "inductive-at-the-constants" && field envelope "assurance" == "externally-attested"
          && (match Zil.Plugin.Evidence.validate envelope with | .ok _ => true | .error _ => false))
  | _ => t.expect "LockStep: the evidence exists" false
  let fault ← Induct.run (lockStep "CInitFault" "StrongInit" "IndInv") tool
  t.expect "LockStep: with the defect switched on the step fails" (match fault with | .notInductive .. => true | _ => false)
  for outcome in [weak, strong, fault] do
    remove outcome.last
    match outcome with
    | .holds base _ | .notInductive base _ | .baseFails base => remove base
    | .stopped _ _ => pure ()

/-- Run the tests; the last group only with `withTool`. -/
def run (withTool : Bool) : IO Bool := do
  let t ← Tally.new
  traceTests t
  runnerTests t
  evidenceTests t
  inductionTests t
  if withTool then realToolTests t
  t.finish

end ZilLib.Test.Apalache
