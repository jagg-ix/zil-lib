import ZilLib.Test.Certify

/-!
Run from the repository root: `lake exe zilLibCertifyTests`. To hunt for disagreements between the engine and the evaluator that has a
proof on more programs: `lake exe zilLibCertifyTests --differential COUNT SEED`.
-/

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--differential", count, seed] =>
      match count.toNat?, seed.toNat? with
      | some count, some seed => pure (if ← ZilLib.Test.Certify.run (some (count, seed)) then 0 else 1)
      | _, _ => IO.eprintln "usage: zilLibCertifyTests [--differential COUNT SEED]"; pure 2
  | [] => pure (if ← ZilLib.Test.Certify.run then 0 else 1)
  | _ => IO.eprintln "usage: zilLibCertifyTests [--differential COUNT SEED]"; pure 2
