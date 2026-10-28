import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicCoordinatePower

/-! # Normal Power Differential Ideal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.NormalPowerDifferentialIdeal.Construction

noncomputable section

/-! Differentiating the control power of a smooth normal recovers its exact principal ideal. -/

variable (k : Type*) {R : Type*} [CommRing k] [CommRing R] [Algebra k R] [Algebra ℚ R]

theorem coordinate_mem_relative_differential_of_power
    (D : Derivation k R R) (z : R) (hD : D z = 1) (J : Ideal R) (n : ℕ)
    (hz : z ^ (n + 1) ∈ J) : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n := by
  have h := Relative.CoefficientIdeal.Construction.iterated_relative_derivation_mem_differential k D J (z ^ (n + 1)) hz n
  change (D.restrictScalars ℤ)^[n] (z ^ (n + 1)) ∈ _ at h
  rw [LogarithmicCoordinatePower.Construction.iteratedRingDerivation_penultimate_power (D.restrictScalars ℤ) z hD n] at h
  exact (Ideal.unit_mul_mem_iff_mem _ (DerivativeHypersurfacePersistence.Construction.factorial_isUnit_of_rationalAlgebra (n + 1))).mp h

theorem normal_power_differential_ideal
    (D : Derivation k R R) (z : R) (hD : D z = 1) (n : ℕ) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k ((Ideal.span {z}) ^ (n + 1)) n = Ideal.span {z} := by
  apply le_antisymm
  · have h := (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary k ((Ideal.span {z}) ^ (n + 1)) n).trans
      (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow (Ideal.span {z}) ((Ideal.span {z}) ^ (n + 1)) 1 n
        (by rw [Nat.add_comm 1 n]))
    simpa only [pow_one] using h
  · apply Ideal.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact coordinate_mem_relative_differential_of_power k D z hD _ n
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self z) (n + 1))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.NormalPowerDifferentialIdeal.Construction
