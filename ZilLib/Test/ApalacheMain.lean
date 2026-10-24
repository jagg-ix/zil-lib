import ZilLib.Test.Apalache

/-!
Run from the repository root: `lake exe zilLibApalacheTests [--with-tool]`. Without `--with-tool` nothing starts a JVM.
-/

def main (args : List String) : IO UInt32 := do
  pure (if ← ZilLib.Test.Apalache.run (args.contains "--with-tool") then 0 else 1)
