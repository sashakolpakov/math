import Mathlib.Data.Nat.Basic

/-! # Scaling Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ScalingDescent

/-! Eventual vanishing descends to all positive exponents when vanishing descends through multiplication of the exponent by a fixed integer greater than one. -/

theorem powerScalingDescent (P : ℕ → Prop) {d : ℕ} (hd : 1 < d)
    (step : ∀ m, P (m * d) → P m) (eventual : ∃ B, ∀ m, B ≤ m → P m)
    (m : ℕ) (hm : 0 < m) : P m := by
  obtain ⟨B, hB⟩ := eventual
  have hiter : ∀ k, P (m * d ^ k) → P m := by
    intro k
    induction k with
    | zero => simpa only [Nat.pow_zero, Nat.mul_one] using (id : P m → P m)
    | succ k ih =>
        intro h
        apply ih
        apply step
        simpa only [Nat.pow_succ, Nat.mul_assoc] using h
  apply hiter B
  apply hB
  exact Nat.le_trans (Nat.le_of_lt (Nat.lt_pow_self hd)) (Nat.le_mul_of_pos_left (d ^ B) hm)

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ScalingDescent
