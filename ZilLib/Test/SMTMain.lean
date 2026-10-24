import ZilLib.Test.SMT

/-!
Run from the repository root: `lake exe zilLibSmtTests [--with-tool]`.
Tests SMT-LIB 2 text generation, model parsing, trace reconstruction, Lean replay validation,
canonical evidence emission, and live Z3 solver execution.
-/

def main (args : List String) : IO UInt32 := do
  pure (if ← ZilLib.Test.SMT.run (args.contains "--with-tool") then 0 else 1)
