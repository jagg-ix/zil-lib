import Zil.Parser.DeclarationProgram
import Zil.Core.Program
import ZilLib.LeanFacts

/-!
# Reading a model

The toolkit sees a model only through the `Zil` library of the pinned core: it parses, expands macros and reads the
resulting program. Nothing here changes the core, and the core knows nothing of this package.
-/

namespace ZilLib

/-- The text of a model file, with the lines of the Lean command `zil_fact` rewritten to `.zc` facts (`ZilLib.LeanFacts`). -/
private def readModel (path : String) : IO String := do
  match ZilLib.LeanFacts.translate (← IO.FS.readFile path) with
  | .ok text => pure text
  | .error problem => throw (IO.userError s!"{path}: {problem}")

/-- The macro libraries at `path`, as the core's `--lib` reads them: the `.zc` files of a directory, sorted by name, or one `.zc` file.
A directory without any is an error, because a mistyped path would otherwise only show later as an unknown macro. -/
def loadLibraries (path : String) : IO (Array Zil.Parser.MacroProgram.LibrarySource) := do
  let location := System.FilePath.mk path
  if ← location.isDir then
    let entries ← location.readDir
    let files := (entries.filter fun entry => entry.fileName.endsWith ".zc")
      |>.qsort (fun left right => left.fileName < right.fileName)
    if files.isEmpty then throw (IO.userError s!"{path}: the directory has no .zc files")
    files.mapM fun entry => do pure { label := "lib/" ++ entry.fileName, text := ← IO.FS.readFile entry.path }
  else
    pure #[{ label := "lib/" ++ (location.fileName.getD path), text := ← IO.FS.readFile location }]

/-- What the core's parser makes of a model file once the macro libraries at `libraryPaths` (in this order) are prepended to it:
the program, with macros expanded. -/
def loadProgramWith (libraryPaths : List String) (path : String) : IO Zil.Program := do
  let text ← readModel path
  let parsed ← if libraryPaths.isEmpty then pure (Zil.Parser.DeclarationProgram.parseText text) else do
    let libraries ← libraryPaths.foldlM (fun all libraryPath => do pure (all ++ (← loadLibraries libraryPath))) #[]
    pure (Zil.Parser.DeclarationProgram.parseTextWithLibraries libraries path text)
  match parsed with
  | .ok program => pure program
  | .error error => throw (IO.userError error.render)

/-- What the core's parser makes of a model file: the program, with macros expanded. -/
def loadProgram (path : String) : IO Zil.Program := loadProgramWith [] path

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
