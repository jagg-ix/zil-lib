/-!
# A small harness for the executable tests

Each test calls `Tally.expect` with a name and a condition; the run prints one line for each and a count, and fails if any condition
did not hold. Tests are run from the repository root, because they read fixtures.
-/

namespace ZilLib.Test

structure Tally where
  passed : IO.Ref Nat
  failed : IO.Ref (Array String)

def Tally.new : IO Tally := do
  pure { passed := ← IO.mkRef 0, failed := ← IO.mkRef #[] }

def Tally.expect (tally : Tally) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then
    tally.passed.modify (· + 1)
    IO.println s!"PASS  {name}"
  else
    tally.failed.modify (·.push name)
    IO.eprintln s!"FAIL  {name}{if detail.isEmpty then "" else ": " ++ detail}"

/-- Print the count and say whether every test passed. -/
def Tally.finish (tally : Tally) : IO Bool := do
  let passed ← tally.passed.get
  let failed ← tally.failed.get
  IO.println s!"{passed} passed, {failed.size} failed"
  pure failed.isEmpty

/-- Does `text` contain `needle`? -/
def contains (text needle : String) : Bool := (text.splitOn needle).length > 1

end ZilLib.Test
