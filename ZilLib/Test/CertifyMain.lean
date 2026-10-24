import ZilLib.Test.Certify

/-!
Run from the repository root: `lake exe zilLibCertifyTests`.
-/

def main : IO UInt32 := do
  pure (if ← ZilLib.Test.Certify.run then 0 else 1)
