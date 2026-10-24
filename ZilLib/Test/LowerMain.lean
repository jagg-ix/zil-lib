import ZilLib.Test.Lower

/-!
Run from the repository root: `lake exe zilLibLowerTests [--with-tool]`.
Tests Batch 2 targets: APL-12, APL-13, APL-14, APL-22, APL-23, CERT-12.
Includes 1,000 random-program differential oracle check and witness replay.
-/

def main (args : List String) : IO UInt32 := do
  pure (if ← ZilLib.Test.Lower.run (args.contains "--with-tool") then 0 else 1)
