import ZilLib.Model
import ZilLib.CLI.ApalacheCommands
import ZilLib.CLI.CertifyCommands
import ZilLib.CLI.SMTCommands
import ZilLib.CLI.CheckCommands
import ZilLib.CLI.UniversalCommands
import ZilLib.CLI.TraceCommands
import ZilLib.CLI.NonInterferenceCommands

/-!
# `zilLib`

    zilLib summary <model.zc>
    zilLib apalache version|check|induct|trace ...      (see ZilLib/CLI/ApalacheCommands.lean)
    zilLib certify <model.zc> [trace.txt]               (see ZilLib/CLI/CertifyCommands.lean)
    zilLib smt version|check|induct ...                 (see ZilLib/CLI/SMTCommands.lean)
    zilLib typecheck <model.zc>                         (see ZilLib/CLI/CheckCommands.lean)
    zilLib check <model.zc> [--inv QUERY] ...           (see ZilLib/CLI/CheckCommands.lean)
    zilLib universal <model.zc> [--inv QUERY] ...       (see ZilLib/CLI/UniversalCommands.lean)
    zilLib trace <model.zc> [--inv QUERY] ...           (see ZilLib/CLI/TraceCommands.lean)
    zilLib noninterference <model.zc> ...               (see ZilLib/CLI/NonInterferenceCommands.lean)

Prints the number of facts, rules, queries and declarations of a model. Further commands arrive with the targets in
`docs/targets.md`; this one shows that the package reads a model through the pinned core and nothing else.
-/

def main (args : List String) : IO UInt32 := do
  match args with
  | ["summary", path] =>
      try
        let summary := ZilLib.summarize (← ZilLib.loadProgram path)
        IO.println s!"facts: {summary.facts}"
        IO.println s!"rules: {summary.rules}"
        IO.println s!"queries: {summary.queries}"
        IO.println s!"declarations: {summary.declarations}"
        pure 0
      catch error : IO.Error =>
        IO.eprintln (toString error)
        pure 2
  | "apalache" :: rest => ZilLib.CLI.ApalacheCommands.run rest
  | "certify" :: rest => ZilLib.CLI.CertifyCommands.run rest
  | "smt" :: rest => ZilLib.CLI.SMTCommands.run rest
  | "typecheck" :: rest => ZilLib.CLI.CheckCommands.runTypecheck rest
  | "check" :: rest => ZilLib.CLI.CheckCommands.runCheck rest
  | "universal" :: rest => ZilLib.CLI.UniversalCommands.runUniversal rest
  | "trace" :: rest => ZilLib.CLI.TraceCommands.run rest
  | "noninterference" :: rest => ZilLib.CLI.NonInterferenceCommands.run rest
  | _ =>
      IO.eprintln "zilLib summary <model.zc>"
      IO.eprintln ZilLib.CLI.ApalacheCommands.usage
      IO.eprintln ZilLib.CLI.CertifyCommands.usage
      IO.eprintln ZilLib.CLI.SMTCommands.usage
      IO.eprintln ZilLib.CLI.CheckCommands.usage
      IO.eprintln ZilLib.CLI.UniversalCommands.usage
      IO.eprintln ZilLib.CLI.TraceCommands.usage
      IO.eprintln ZilLib.CLI.NonInterferenceCommands.usage
      pure 2
