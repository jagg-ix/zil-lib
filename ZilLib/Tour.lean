/-!
# A claim worth a proof

`examples/tour/04-claims-need-proofs.zc` says a checkout rule is safe and names this theorem as its proof. The ZIL audit only checks that a
high-criticality claim names a Lean theorem; that the theorem says what the claim says is Lean's job, done here by the kernel.
-/

namespace ZilLib.Tour

/-- Taking a percentage off a price never gives more than the price. -/
theorem discounted_le (price pct : Nat) (_h : pct ≤ 100) : price * (100 - pct) / 100 ≤ price := by
  apply Nat.div_le_of_le_mul
  calc price * (100 - pct) ≤ price * 100 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = 100 * price := Nat.mul_comm _ _

end ZilLib.Tour
