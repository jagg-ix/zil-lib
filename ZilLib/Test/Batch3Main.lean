import ZilLib.Test.Batch3

/-!
Run from the repository root: `lake exe zilLibBatch3Tests [--with-tool]`.
Tests Batch 3 targets: APL-05 (Check vocabulary macro extension) and APL-30 (Universal contract checking S1).
-/

def main (args : List String) : IO UInt32 := do
  pure (if ← ZilLib.Test.Batch3.run (args.contains "--with-tool") then 0 else 1)
