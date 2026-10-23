import ZilLib.Test.ModelSubstrate

/-!
The tests are `run_cmd` blocks that run while their module is compiled and read the library files under `libsets/`;
building this executable is running them. A failing test is a build error that names the test.
-/

def main : IO UInt32 := do
  IO.println "zilLibTests: the model substrate tests passed while compiling"
  pure 0
