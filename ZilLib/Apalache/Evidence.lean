import Zil.Plugin.Evidence
import ZilLib.Apalache.Run

/-!
# Evidence of a run

A run of the tool is recorded as a `ZIL-EVIDENCE/1` envelope (`spec/evidence-envelope-v1.md` of the core), built by the core's own
`Zil.Plugin.Evidence.make` so that the core's checks accept it. The producer is outside Lean, so the authority is `external` and the
assurance `externally-attested`; nothing here is `validated` or `kernel-backed`.

What the identity covers, and what it leaves out:

* `input_sha256` covers the model and the modules it extends, the parameters of the request (initial and next-state predicates,
  invariants, constants, bound) and the version of the tool. Changing any of them changes the evidence identifier.
* `output_sha256` covers the payload: the kind of run, the verdict, the tool's outcome and a sentence that states the bound.
* The metadata (command, exit code, time, the digest of the trace) is not part of the identity, because it varies from run to run.

A run that did not finish is evidence of nothing but that it did not finish, so a timeout is recorded as `inconclusive-timeout`
and never as a pass. A run the tool rejected, or that could not start, says nothing about the model and has no envelope.
-/

namespace ZilLib.Apalache.Evidence

open Zil.Json Zil.Crypto

/-- The version of this package, as `lakefile.lean` declares it. -/
def version : String := "0.1.0"

/-- The extension that produces the envelopes. -/
def manifest : Zil.Plugin.Manifest :=
  { id := "extension:zil-lib-apalache", version, runtime := "external", entrypoint := toolName,
    capabilities := #["bounded-model-checking"], authority := "external", trusted := false }

/-- The role of the producer in an envelope. -/
def role : String := "bounded-model-checker"

private def sha256 (bytes : ByteArray) : String := "sha256:" ++ Sha256.hex bytes

/-- The names after `EXTENDS` in the module's text. Only the first such line is read, and a name list that continues on the next
line is not followed. -/
def extendedNames (text : String) : Array String :=
  match (text.splitOn "\n").find? (·.startsWith "EXTENDS") with
  | none => #[]
  | some line =>
      let names := (String.ofList (line.toList.drop 7)).splitOn ","
      (names.map fun name => String.ofList (name.toList.filter fun c => !c.isWhitespace)).toArray.filter (!·.isEmpty)

/-- The model and, next to it, the modules it extends, by file name and digest. Standard modules have no file there. -/
partial def moduleDigests (model : System.FilePath) : IO (Array (String × String)) := do
  let directory := model.parent.getD "."
  let mut seen : Array String := #[]
  let mut pending : Array System.FilePath := #[model]
  let mut found : Array (String × String) := #[]
  while h : pending.size > 0 do
    let file := pending.back
    pending := pending.pop
    let name := file.fileName.getD file.toString
    if seen.contains name then continue
    seen := seen.push name
    let bytes ← IO.FS.readBinFile file
    found := found.push (name, sha256 bytes)
    for extended in extendedNames (String.fromUTF8! bytes) do
      let candidate := directory / s!"{extended}.tla"
      if ← candidate.pathExists then pending := pending.push candidate
  pure (found.qsort (·.1 < ·.1))

/-- What a run claims, before it is put in an envelope. -/
structure Claim where
  /-- `check` or `induction`. -/
  kind : String
  verdict : String
  /-- The words that state the bound the verdict holds within. -/
  statement : String
  outcome : Option String
  /-- The request: init, next, invariants, constants and bounds, as the tool is asked. -/
  parameters : J
  toolVersion : String
  /-- Facts about this run that are not part of the identity. -/
  metadata : J

/-- Put a claim about the model in `model` in an envelope. -/
def envelope (model : System.FilePath) (subjectDetail : String) (claim : Claim) : IO (Except String J) := do
  let modules ← moduleDigests model
  let moduleList := J.arr (modules.map fun (file, digest) => J.obj #[("file", .str file), ("sha256", .str digest)])
  let inputs := J.obj #[("modules", moduleList), ("parameters", claim.parameters), ("tool_version", .str claim.toolVersion)]
  let payload := J.obj #[("kind", .str claim.kind), ("verdict", .str claim.verdict), ("outcome", claim.outcome.map J.str |>.getD .null),
    ("statement", .str claim.statement)]
  let inputText ← match Zil.Json.canonical inputs, Zil.Json.canonical payload with
    | .ok inputs, .ok payload => pure (some (Zil.Json.write inputs, Zil.Json.write payload))
    | _, _ => pure none
  let some (inputText, payloadText) := inputText | return .error "the request could not be put in canonical form"
  let metadata := J.obj #[("model", .str (model.fileName.getD model.toString)), ("modules", moduleList), ("parameters", claim.parameters),
    ("run", claim.metadata)]
  return Zil.Plugin.Evidence.make
    { manifest, role, subject := s!"{claim.kind}:{model.fileName.getD model.toString}:{subjectDetail}",
      inputSha256 := some (Sha256.ofText inputText), payload := payloadText, metadata }

/-! ## One `check` -/

/-- The verdict of a run as the evidence names it. A run that rejected its input or could not start has none. -/
def checkVerdict : Verdict → Option String
  | .noError => some "no-violation-within-bound"
  | .tooShort => some "no-violation-no-execution-of-the-requested-length"
  | .violation => some "violation-found"
  | .deadlock => some "deadlock-found"
  | .timedOut => some "inconclusive-timeout"
  | .failed _ | .rejected _ | .unavailable _ => none

private def listOf (items : Array String) : J := .arr (items.map .str)

private def optionalName (name : Option String) : J := name.map J.str |>.getD .null

/-- The parameters of a `check`, as they enter the identity. -/
def checkParameters (config : Config) : J :=
  .obj #[("cinit", optionalName config.cinit), ("init", optionalName config.init), ("inv", listOf config.inv),
    ("length", .int config.length), ("next", optionalName config.next), ("no_deadlock", .bool config.noDeadlock)]

private def statementOf (config : Config) (verdict : String) : String :=
  let invariants := ", ".intercalate config.inv.toList
  let constants := match config.cinit with | some name => s!" with the constants set by {name}" | none => ""
  match verdict with
  | "no-violation-within-bound" =>
      s!"no execution of {config.length} steps from {config.init.getD "Init"} violates {invariants}{constants}; this says nothing about longer executions"
  | "no-violation-no-execution-of-the-requested-length" =>
      s!"no violation of {invariants}{constants}, but no execution reaches {config.length} steps"
  | "violation-found" => s!"an execution of at most {config.length} steps violates {invariants}{constants}"
  | "deadlock-found" => s!"a state reachable in at most {config.length} steps has no successor{constants}"
  | _ => s!"the run did not finish within its deadline, so nothing is known about {invariants}{constants}"

/-- The facts of a run that do not enter the identity. -/
def runMetadata (result : Result) : J :=
  .obj #[("command", listOf result.command), ("elapsed_ms", .int result.elapsedMs),
    ("exit_code", result.exitCode.map (fun code => J.int code) |>.getD .null), ("tool", .str toolName),
    ("trace_sha256", result.traceText.map (fun text => J.str (Sha256.ofText text)) |>.getD .null)]

/-- The envelope for a `check`, or `none` when the run says nothing about the model. -/
def ofCheck (config : Config) (result : Result) : IO (Option (Except String J)) := do
  let some verdict := checkVerdict result.verdict | return none
  let toolVersion := result.tool.map (·.version) |>.getD ""
  some <$> envelope config.model (",".intercalate config.inv.toList)
    { kind := "check", verdict, statement := statementOf config verdict, outcome := result.outcome,
      parameters := checkParameters config, toolVersion, metadata := runMetadata result }

end ZilLib.Apalache.Evidence
