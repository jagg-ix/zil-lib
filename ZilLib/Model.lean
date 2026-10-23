import Zil.Parser.DeclarationProgram
import Zil.Core.Program

/-!
# Reading a model

The toolkit sees a model only through the `Zil` library of the pinned core: it parses, expands macros and reads the
resulting program. Nothing here changes the core, and the core knows nothing of this package.
-/

namespace ZilLib

/-- What the core's parser makes of a model file: the program, with macros expanded. -/
def loadProgram (path : String) : IO Zil.Program := do
  match ← Zil.Parser.DeclarationProgram.parseFile path with
  | .ok program => pure program
  | .error error => throw (IO.userError error.render)

/-- Counts of what a model holds, for a quick look and for the skeleton's gate. -/
structure Summary where
  facts : Nat
  rules : Nat
  queries : Nat
  declarations : Nat

def summarize (program : Zil.Program) : Summary :=
  { facts := program.facts.size, rules := program.rules.size, queries := program.queries.size,
    declarations := program.declarations.size }

end ZilLib
