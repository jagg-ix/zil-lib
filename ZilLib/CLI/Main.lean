import ZilLib.Model
import ZilLib.CLI.ApalacheCommands

/-!
# `zilLib`

    zilLib summary <model.zc>
    zilLib apalache version|check|induct|trace ...      (see ZilLib/CLI/ApalacheCommands.lean)

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
  | _ =>
      IO.eprintln "zilLib summary <model.zc>"
      IO.eprintln ZilLib.CLI.ApalacheCommands.usage
      pure 2
