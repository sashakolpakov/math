import Mathlib.RingTheory.WittVector.DiscreteValuationRing

/-! # Prime Weight Units -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.PrimeWeightUnits.WittPrimeWeightUnits

noncomputable section

/-!
# Integral inverses of polynomial weights prime to p

Weights not divisible by p are units in the actual Witt ring. Their
inverses stay integral and are fixed by coefficient endomorphisms;
they will supply the bounded coordinate homotopies in Frobenius descent.
-/

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]

theorem isUnit (n : ℕ) (h : ¬ p ∣ n) : IsUnit (n : WittVector p k) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  change (WittVector.constantCoeff (n : WittVector p k) : k) ≠ 0
  rw [map_natCast]
  exact (CharP.cast_eq_zero_iff k p n).not.mpr h

def inverse (n : ℕ) : WittVector p k :=
  if h : p ∣ n then 0 else ↑((isUnit p k n h).unit⁻¹)

theorem mul_inverse (n : ℕ) : (n : WittVector p k) * inverse p k n = if p ∣ n then 0 else 1 := by
  classical
  by_cases h : p ∣ n
  · simp [inverse, h]
  · rw [inverse, dite_eq_right h, ite_eq_right h]
    exact (Units.mul_inv_eq_one (u := (isUnit p k n h).unit)).mpr
      (isUnit p k n h).unit_spec.symm

theorem inverse_mul (n : ℕ) : inverse p k n * (n : WittVector p k) = if p ∣ n then 0 else 1 := by
  rw [mul_comm, mul_inverse]

theorem fixed (f : WittVector p k →+* WittVector p k) (n : ℕ) : f (inverse p k n) = inverse p k n := by
  classical
  by_cases h : p ∣ n
  · simp [inverse, h]
  · apply (isUnit p k n h).mul_left_cancel
    have hm : (n : WittVector p k) * inverse p k n = 1 := by rw [mul_inverse, ite_eq_right h]
    calc
      (n : WittVector p k) * f (inverse p k n) = f ((n : WittVector p k) * inverse p k n) := by
        rw [map_mul, map_natCast]
      _ = 1 := by rw [hm, map_one]
      _ = (n : WittVector p k) * inverse p k n := hm.symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.PrimeWeightUnits.WittPrimeWeightUnits
