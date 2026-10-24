import Zil.Process.Run
import ZilLib.Apalache.Itf

/-!
# Running Apalache

The tool is found on the machine and never fetched or vendored: `APALACHE_HOME/bin/apalache-mc` first, then every directory of
`PATH`. A run happens in a fresh output directory, under a deadline, with no shell. A tool that is absent, or that fails to report
its version, is a result and not an error, so that a gate without the tool can say so and go on.

What the tool does with its exit code was observed on Apalache 0.62.4 (`docs/tool-notes.md`): 0 for no error, 12 for a violated
invariant and for a deadlock (the line `The outcome is: ...` tells them apart), 255 for input it rejects. Another code is reported
as a failure of the run, not interpreted.
-/

namespace ZilLib.Apalache

/-- The name of the executable. -/
def toolName : String := "apalache-mc"

/-- A tool found on the machine, with the version it reports. -/
structure Tool where
  path : System.FilePath
  version : String
  deriving Inhabited

/-- What the search for the tool found. -/
inductive Located where
  | found (tool : Tool)
  | missing
  /-- An executable of that name exists but did not report a version. -/
  | broken (path : System.FilePath) (detail : String)
  deriving Inhabited

/-- Look for the tool in `home/bin` and then in each directory of `searchPath`, and ask the first one found for its version. -/
def locate (home : Option String) (searchPath : System.SearchPath) : IO Located := do
  let candidates := (home.map fun directory => System.FilePath.mk directory / "bin" / toolName).toList
    ++ searchPath.map (· / toolName)
  for candidate in candidates do
    if (← candidate.pathExists) && !(← candidate.isDir) then
      try
        let result ← Zil.Process.run candidate.toString #["version"] 120000
        if result.exitCode != 0 then
          return .broken candidate s!"`version` exited with {result.exitCode}"
        let version := ((result.stdout.splitOn "\n").headD "")
        return .found { path := candidate, version := String.ofList (version.toList.filter fun c => !c.isWhitespace) }
      catch error =>
        return .broken candidate (toString error)
  return .missing

/-- Look where the environment says: `APALACHE_HOME`, then `PATH`. -/
def locateInEnvironment : IO Located := do
  locate (← IO.getEnv "APALACHE_HOME") (System.SearchPath.parse ((← IO.getEnv "PATH").getD ""))

/-- What one `check` is asked to do. The names are the tool's: `--init`, `--next`, `--inv`, `--cinit`, `--length`. -/
structure Config where
  model : System.FilePath
  init : Option String := none
  next : Option String := none
  inv : Array String := #[]
  cinit : Option String := none
  length : Nat := 10
  /-- Do not report a state without a successor as a violation (`--no-deadlock`). -/
  noDeadlock : Bool := false
  timeoutMs : Nat := 600000
  /-- Where the tool writes; a new temporary directory when absent. -/
  outDir : Option System.FilePath := none
  deriving Inhabited

/-- The arguments of `apalache-mc` for this request. -/
def Config.arguments (config : Config) (outDir : System.FilePath) : Array String :=
  #["check"]
    ++ (config.init.map (s!"--init=" ++ ·)).toArray
    ++ (config.next.map (s!"--next=" ++ ·)).toArray
    ++ (if config.inv.isEmpty then #[] else #[s!"--inv={",".intercalate config.inv.toList}"])
    ++ (config.cinit.map (s!"--cinit=" ++ ·)).toArray
    ++ #[s!"--length={config.length}"]
    ++ (if config.noDeadlock then #["--no-deadlock"] else #[])
    ++ #[s!"--out-dir={outDir}", config.model.toString]

/-- What a run came to. -/
inductive Verdict where
  /-- Exit 0: no violation in any execution of the requested length. -/
  | noError
  /-- Exit 0 with the outcome `ExecutionsTooShort`: no violation, but no execution reaches the requested length. -/
  | tooShort
  /-- Exit 12: an invariant is violated; a trace is written. -/
  | violation
  /-- Exit 12 with the outcome `Deadlock`: a reachable state has no successor. -/
  | deadlock
  /-- The tool ran and failed with this code, for example 255 for input it rejects. -/
  | failed (code : Nat)
  /-- The deadline passed and the tool was killed. -/
  | timedOut
  /-- The request was refused before the tool was called. -/
  | rejected (reason : String)
  /-- There is no tool to run, or it did not report a version. -/
  | unavailable (reason : String)
  deriving Repr, BEq, Inhabited

/-- Everything a run left behind. Nothing here is a proof: see `docs/targets.md` on what a result may be called. -/
structure Result where
  verdict : Verdict
  /-- The word after `The outcome is:` in the tool's output. -/
  outcome : Option String := none
  exitCode : Option Nat := none
  tool : Option Tool := none
  /-- The executable and its arguments. -/
  command : Array String := #[]
  stdout : String := ""
  stderr : String := ""
  outDir : Option System.FilePath := none
  trace : Option Itf.Trace := none
  /-- The text of the trace file, for digests. -/
  traceText : Option String := none
  /-- Why a trace that was written could not be read. -/
  traceProblem : Option String := none
  elapsedMs : Nat := 0
  deriving Inhabited

/-- The word after `The outcome is: ` in the tool's output. -/
def outcomeOf (stdout : String) : Option String :=
  (stdout.splitOn "\n").findSome? fun line =>
    match line.splitOn "The outcome is: " with
    | [_, rest] => some (String.ofList (rest.toList.takeWhile Char.isAlphanum))
    | _ => none

/-- Read the exit code and the outcome as a verdict. -/
def verdictOf (exitCode : Nat) (outcome : Option String) : Verdict :=
  match exitCode with
  | 0 => if outcome == some "ExecutionsTooShort" then .tooShort else .noError
  | 12 => if outcome == some "Deadlock" then .deadlock else .violation
  | code => .failed code

private partial def filesUnder (directory : System.FilePath) : IO (Array System.FilePath) := do
  let mut found := #[]
  for entry in ← directory.readDir do
    if ← entry.path.isDir then found := found ++ (← filesUnder entry.path)
    else found := found.push entry.path
  pure found

/-- The newest `violation.itf.json` under an output directory. The tool writes to `<model file name>/<timestamp>_<id>/`, and the
timestamps sort as text. -/
def newestTrace (outDir : System.FilePath) : IO (Option System.FilePath) := do
  let candidates := (← filesUnder outDir).filter (·.fileName == some "violation.itf.json")
  pure (candidates.qsort (·.toString < ·.toString)).back?

/-- Run `check` once. -/
def check (config : Config) (tool : Tool) : IO Result := do
  let started ← IO.monoMsNow
  let finish (result : Result) : IO Result := do
    pure { result with elapsedMs := (← IO.monoMsNow) - started }
  let refuse (reason : String) : IO Result := finish { verdict := .rejected reason, tool := some tool }
  unless ← config.model.pathExists do return ← refuse s!"{config.model} does not exist"
  -- The tool makes a directory named after the model file inside the output directory (and fails with 255 if the model is in it).
  let modelDirectory ← IO.FS.realPath (config.model.parent.getD ".")
  let outDir ← match config.outDir with
    | some directory => do IO.FS.createDirAll directory; pure directory
    | none => IO.FS.createTempDir
  if (← IO.FS.realPath outDir) == modelDirectory then
    return ← refuse "the output directory is the directory of the model; the tool creates a directory named after the model there"
  let arguments := config.arguments outDir
  let command := #[tool.path.toString] ++ arguments
  try
    let run ← Zil.Process.run tool.path.toString arguments config.timeoutMs
    let exitCode := run.exitCode.toNat
    let outcome := outcomeOf run.stdout
    let verdict := verdictOf exitCode outcome
    let mut result : Result :=
      { verdict, outcome, exitCode := some exitCode, tool := some tool, command, stdout := run.stdout, stderr := run.stderr,
        outDir := some outDir }
    if verdict == .violation || verdict == .deadlock then
      if let some file ← newestTrace outDir then
        let text ← IO.FS.readFile file
        match Itf.Trace.parse text with
        | .ok trace => result := { result with trace := some trace, traceText := some text }
        | .error problem => result := { result with traceText := some text, traceProblem := some problem }
      else
        result := { result with traceProblem := some "the tool wrote no violation.itf.json" }
    finish result
  catch error =>
    let message := toString error
    if message.startsWith "external-tool-timeout" then
      finish { verdict := .timedOut, tool := some tool, command, outDir := some outDir }
    else
      finish { verdict := .unavailable message, tool := some tool, command, outDir := some outDir }

/-- Locate the tool where the environment says, and run `check`; an absent tool is a result. -/
def checkWithEnvironment (config : Config) : IO Result := do
  match ← locateInEnvironment with
  | .found tool => check config tool
  | .missing => pure { verdict := .unavailable s!"{toolName} was not found in APALACHE_HOME or PATH" }
  | .broken path detail => pure { verdict := .unavailable s!"{path}: {detail}" }

end ZilLib.Apalache
