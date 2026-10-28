import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

/-! # Ring Power Linearization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RingPowerLinearization

noncomputable section

/-! The first-order part of a power of one plus an element in an arbitrary, possibly noncommutative, ring. -/

universe u

variable {R : Type u} [Ring R]

theorem ringPower_linearization (x : R) (n : ℕ) :
    ∃ z : R, (1 + x) ^ n = 1 + n • x + x ^ 2 * z := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨z + n • (1 : R) + z * x, ?_⟩
    rw [pow_succ, hz, succ_nsmul]
    simp only [mul_add, add_mul, one_mul, mul_one, pow_two, smul_mul_assoc, mul_smul_comm, mul_assoc]
    abel

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RingPowerLinearization
