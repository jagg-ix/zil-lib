import ZilLib.Apalache

/-!
# `zilLib apalache`

    zilLib apalache version
    zilLib apalache check MODEL.tla --inv A,B [--init I] [--next N] [--cinit C] [--length N] [--no-deadlock]
                          [--timeout SECONDS] [--out-dir DIR] [--evidence FILE]
    zilLib apalache induct MODEL.tla --indinit IndInit --inv Inv [--cinit C] [--init I] [--next N]
                          [--timeout SECONDS] [--evidence FILE]
    zilLib apalache trace TRACE.itf.json

Exit codes: 0 no violation within the bound (or the invariant is inductive), 1 a violation, a deadlock or an invariant that is
not inductive, 2 input the tool rejects, a failed run or a wrong command line, 3 no tool, 4 the deadline passed.
-/

namespace ZilLib.CLI.ApalacheCommands

open ZilLib.Apalache Zil.Json

def usage : String :=
  "zilLib apalache version\n" ++
  "zilLib apalache check MODEL.tla --inv A,B [--init I] [--next N] [--cinit C] [--length N] [--no-deadlock]\n" ++
  "                      [--timeout SECONDS] [--out-dir DIR] [--evidence FILE]\n" ++
  "zilLib apalache induct MODEL.tla --indinit IndInit --inv Inv [--cinit C] [--init I] [--next N]\n" ++
  "                      [--timeout SECONDS] [--evidence FILE]\n" ++
  "zilLib apalache trace TRACE.itf.json"

/-- The exit code a verdict is reported with. -/
def exitCodeOf : Verdict → UInt32
  | .noError | .tooShort => 0
  | .violation | .deadlock => 1
  | .failed _ | .rejected _ => 2
  | .unavailable _ => 3
  | .timedOut => 4

/-- A command line split into its positional arguments, its options with a value and its flags. -/
structure Parsed where
  positional : Array String := #[]
  options : Array (String × String) := #[]
  flags : Array String := #[]

def parseArguments (args : List String) (valued flags : List String) : Except String Parsed := do
  let mut parsed : Parsed := {}
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | [] => pure ()
    | argument :: tail =>
        if argument.startsWith "--" then
          if flags.contains argument then
            parsed := { parsed with flags := parsed.flags.push argument }
            rest := tail
          else if valued.contains argument then
            match tail with
            | value :: tail' =>
                parsed := { parsed with options := parsed.options.push (argument, value) }
                rest := tail'
            | [] => throw s!"{argument} needs a value"
          else throw s!"unknown option {argument}"
        else
          parsed := { parsed with positional := parsed.positional.push argument }
          rest := tail
  pure parsed

private def option? (parsed : Parsed) (name : String) : Option String :=
  (parsed.options.find? (·.1 == name)).map (·.2)

private def seconds (parsed : Parsed) : Except String Nat :=
  match option? parsed "--timeout" with
  | none => pure 600000
  | some text => match text.toNat? with
      | some value => pure (value * 1000)
      | none => throw s!"--timeout needs a number of seconds, not {text}"

private def names (text : String) : Array String :=
  (text.splitOn ",").toArray.filter (!·.isEmpty)

private def tailOf (text : String) (characters : Nat) : String :=
  String.ofList (text.toList.drop (text.length - characters))

/-- Find the tool, or say why there is none. -/
private def withTool (action : Tool → IO UInt32) : IO UInt32 := do
  match ← locateInEnvironment with
  | .found tool => action tool
  | .missing =>
      IO.eprintln s!"tool unavailable: {toolName} was not found in APALACHE_HOME or PATH"
      pure 3
  | .broken path detail =>
      IO.eprintln s!"tool unavailable: {path}: {detail}"
      pure 3

private def writeEvidence (path : Option String) (evidence : Option (Except String J)) : IO Unit := do
  match path, evidence with
  | some file, some (.ok envelope) =>
      IO.FS.writeFile file (Zil.Json.write envelope ++ "\n")
      IO.println s!"evidence: {file} ({(envelope.getStr? "evidence_id").getD ""})"
  | some _, some (.error problem) => IO.eprintln s!"no evidence was written: {problem}"
  | some _, none => IO.println "no evidence was written: this run says nothing about the model"
  | none, _ => pure ()

/-- What a `check` says, in words. -/
def describe (config : Config) (result : Result) : String :=
  let invariants := ", ".intercalate config.inv.toList
  let traceText := match result.trace, result.traceProblem with
    | some trace, _ => trace.render
    | none, some problem => s!"the trace could not be read: {problem}\n"
    | none, none => ""
  match result.verdict with
  | .noError =>
      s!"no violation of {invariants} in any execution of {config.length} steps.\n" ++
      "This says nothing about longer executions, and nothing about other constants.\n"
  | .tooShort =>
      s!"no violation of {invariants}, but no execution reaches {config.length} steps: some state has no successor, so the bound was not fully used.\n"
  | .violation => s!"{invariants} is violated. The counterexample:\n{traceText}"
  | .deadlock => s!"a state has no successor (a deadlock). The execution:\n{traceText}"
  | .failed code => s!"the tool failed with exit code {code}:\n{tailOf result.stdout 800}\n"
  | .timedOut => s!"inconclusive: the deadline passed after {config.timeoutMs / 1000} s. Nothing is known about {invariants}.\n"
  | .rejected reason => s!"not run: {reason}\n"
  | .unavailable reason => s!"tool unavailable: {reason}\n"

def check (args : List String) : IO UInt32 := do
  let parsed ← match parseArguments args ["--inv", "--init", "--next", "--cinit", "--length", "--timeout", "--out-dir", "--evidence"] ["--no-deadlock"] with
    | .ok parsed => pure parsed
    | .error problem => IO.eprintln s!"{problem}\n{usage}"; return 2
  let some model := parsed.positional[0]? | IO.eprintln s!"a model file is needed\n{usage}"; return 2
  let some inv := option? parsed "--inv" | IO.eprintln s!"--inv is needed\n{usage}"; return 2
  let timeoutMs ← match seconds parsed with
    | .ok value => pure value
    | .error problem => IO.eprintln problem; return 2
  let length := (option? parsed "--length").bind String.toNat? |>.getD 10
  let config : Config :=
    { model, init := option? parsed "--init", next := option? parsed "--next", inv := names inv, cinit := option? parsed "--cinit",
      length, noDeadlock := parsed.flags.contains "--no-deadlock", timeoutMs, outDir := (option? parsed "--out-dir").map System.FilePath.mk }
  withTool fun tool => do
    IO.println s!"tool: {toolName} {tool.version} ({tool.path})"
    let result ← ZilLib.Apalache.check config tool
    IO.print (describe config result)
    if let some directory := result.outDir then IO.println s!"output: {directory}"
    writeEvidence (option? parsed "--evidence") (← Evidence.ofCheck config result)
    pure (exitCodeOf result.verdict)

def induct (args : List String) : IO UInt32 := do
  let parsed ← match parseArguments args ["--inv", "--indinit", "--init", "--next", "--cinit", "--timeout", "--evidence"] [] with
    | .ok parsed => pure parsed
    | .error problem => IO.eprintln s!"{problem}\n{usage}"; return 2
  let some model := parsed.positional[0]? | IO.eprintln s!"a model file is needed\n{usage}"; return 2
  let some inv := option? parsed "--inv" | IO.eprintln s!"--inv is needed\n{usage}"; return 2
  let some indInit := option? parsed "--indinit" | IO.eprintln s!"--indinit is needed\n{usage}"; return 2
  let timeoutMs ← match seconds parsed with
    | .ok value => pure value
    | .error problem => IO.eprintln problem; return 2
  let config : Induct.Config :=
    { model, cinit := option? parsed "--cinit", init := (option? parsed "--init").getD "Init",
      next := (option? parsed "--next").getD "Next", indInit, inv := names inv, timeoutMs }
  withTool fun tool => do
    IO.println s!"tool: {toolName} {tool.version} ({tool.path})"
    let outcome ← Induct.run config tool
    IO.print (Induct.report config outcome)
    writeEvidence (option? parsed "--evidence") (← Induct.evidence config outcome)
    pure <| match outcome with
      | .holds .. => 0
      | .baseFails .. | .notInductive .. => 1
      | .stopped _ result => exitCodeOf result.verdict

def trace (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      match ← (IO.FS.readFile path).toBaseIO with
      | .error error => IO.eprintln (toString error); pure 2
      | .ok text =>
          match Itf.Trace.parse text with
          | .ok trace => IO.print trace.render; pure 0
          | .error problem => IO.eprintln s!"{path}: {problem}"; pure 2
  | _ => IO.eprintln usage; pure 2

def version : IO UInt32 :=
  withTool fun tool => do
    IO.println s!"{toolName} {tool.version} ({tool.path})"
    pure 0

def run : List String → IO UInt32
  | "version" :: [] => version
  | "check" :: rest => check rest
  | "induct" :: rest => induct rest
  | "trace" :: rest => trace rest
  | _ => do IO.eprintln usage; pure 2

end ZilLib.CLI.ApalacheCommands
