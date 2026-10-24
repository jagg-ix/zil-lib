import Zil.Process.Run
import ZilLib.TransitionSystem
import ZilLib.SMT.Text
import ZilLib.SMT.Parser

/-!
# SMT Solver Process Runner (TS-03)

Locates and executes SMT-LIB 2 solvers (`z3` by default; supports cvc5 or any SMT-LIB 2 compliant solver).
Manages timeouts (`-T:`), inputs, and raw outputs with zero Python / zero PySMT dependencies.
-/

namespace ZilLib.SMT

/-- SMT solver metadata. -/
structure Tool where
  path : System.FilePath
  name : String
  version : String
  deriving Repr, Inhabited

/-- Result of attempting to locate an SMT solver executable. -/
inductive Located where
  | found (tool : Tool)
  | missing (name : String)
  | broken (path : System.FilePath) (detail : String)
  deriving Inhabited

/-- Check if an executable exists on `searchPath` and reports its version. -/
def locate (solverName : String := "z3") (searchPath : System.SearchPath) : IO Located := do
  let candidates := searchPath.map (· / solverName)
  for candidate in candidates do
    if (← candidate.pathExists) && !(← candidate.isDir) then
      try
        let result ← Zil.Process.run candidate.toString #["--version"] 10000
        if result.exitCode != 0 then
          return .broken candidate s!"'--version' exited with code {result.exitCode}"
        let firstLine := (result.stdout.splitOn "\n").headD "" |>.trimAscii.toString
        return .found { path := candidate, name := solverName, version := firstLine }
      catch err =>
        return .broken candidate (toString err)
  return .missing solverName

/-- Locate SMT solver on system `PATH`. -/
def locateInEnvironment (solverName : String := "z3") : IO Located := do
  let envPath := (← IO.getEnv "PATH").getD ""
  locate solverName (System.SearchPath.parse envPath)

/--
Run an SMT-LIB 2 script string through the solver under a deadline.
Writes the script to a temporary file, invokes the solver, and cleans up the file.
-/
def runSmtScript (tool : Tool) (script : String) (timeoutMs : Nat := 30000) : IO (Except String String) := do
  let tempDir ← IO.FS.createTempDir
  let scriptFile := tempDir / "query.smt2"
  IO.FS.writeFile scriptFile script

  let timeoutSec := max 1 (timeoutMs / 1000)
  let args :=
    if tool.name.contains "z3" then
      #[s!"-T:{timeoutSec}", "-smt2", scriptFile.toString]
    else
      #[scriptFile.toString]

  try
    let res ← Zil.Process.run tool.path.toString args timeoutMs
    try IO.FS.removeDirAll tempDir catch _ => pure ()
    if res.exitCode == 0 then
      pure (.ok res.stdout)
    else
      -- Some solvers exit non-zero on timeout or unknown
      if res.stdout.contains "timeout" || res.stderr.contains "timeout" then
        throw (IO.userError "external-tool-timeout")
      pure (.ok res.stdout)
  catch err =>
    try IO.FS.removeDirAll tempDir catch _ => pure ()
    let msg := toString err
    if msg.startsWith "external-tool-timeout" || msg.contains "timed out" then
      pure (.error "timeout")
    else
      pure (.error msg)

end ZilLib.SMT
