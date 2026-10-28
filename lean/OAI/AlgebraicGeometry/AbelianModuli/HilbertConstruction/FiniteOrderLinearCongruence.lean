import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RingPowerLinearization
import Mathlib.Algebra.Group.Torsion

/-! # Finite Order Linear Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteOrderLinearCongruence

noncomputable section

/-! A finite-order element congruent to one gives a divisibility relation for its first-order coefficient in an additively torsion-free ring. -/

universe u

variable {R : Type u} [Ring R]

theorem ringPower_integerLinearization (x : R) (m n : ℕ) :
    ∃ z : R, (1 + m • x) ^ n = 1 + m • (n • x + m • z) := by
  obtain ⟨z, hz⟩ := RingPowerLinearization.ringPower_linearization (m • x) n
  refine ⟨x ^ 2 * z, ?_⟩
  simpa only [pow_two, smul_mul_assoc, mul_smul_comm, nsmul_add, mul_assoc, add_assoc,
    smul_comm n m x] using hz

theorem ringFiniteOrder_linearCoefficient_divisible [IsAddTorsionFree R]
    (x : R) (m n : ℕ) (hm : m ≠ 0) (h : (1 + m • x) ^ n = 1) :
    ∃ z : R, n • x = m • z := by
  obtain ⟨z, hz⟩ := ringPower_integerLinearization x m n
  have he : (1 : R) + m • (n • x + m • z) = 1 := hz.symm.trans h
  have he' : m • (n • x + m • z) = 0 :=
    add_left_cancel (he.trans (add_zero (1 : R)).symm)
  have hzero : n • x + m • z = 0 := (nsmul_eq_zero_iff_right hm).mp he'
  exact ⟨-z, (eq_neg_of_add_eq_zero_left hzero).trans (smul_neg m z).symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteOrderLinearCongruence
