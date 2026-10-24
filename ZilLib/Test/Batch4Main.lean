import ZilLib.Test.Batch4

/-!
Run from the repository root: `lake exe zilLibBatch4Tests [--with-tool]`.
Tests Batch 4 targets: APL-31 (Operations), APL-32 (Temporal governance S2), and APL-33 (Non-interference S3).
-/

def main (args : List String) : IO UInt32 := do
  pure (if ← ZilLib.Test.Batch4.run (args.contains "--with-tool") then 0 else 1)
