import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalPolarizationApproximation
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BilinearRational

/-! # Polarization From Rational Pairing -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolarizationFromRationalPairing.CM.Construction

noncomputable section

/-! A rational vector-valued alternating pairing whose complexification
has a positive real trace yields a rational weight-one polarization. -/

open scoped TensorProduct

variable {U W : Type*} [AddCommGroup U] [Module ℚ U]
  [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]

theorem exists_polarization_of_positive_rational_pairing (H : WeightOne.CM.WeightOneHodgeStructure U)
    (F : U →ₗ[ℚ] U →ₗ[ℚ] W) (hF : ∀ u, F u u = 0)
    (hiso : ∀ u ∈ H.holomorphic, ∀ v ∈ H.holomorphic,
      LinearMap.BilinMap.baseChange ℂ F u v = 0)
    (T : WeightOne.CM.Complexification W →ₗ[ℂ] ℂ)
    (hT : ∀ w : W, (T ((1 : ℂ) ⊗ₜ[ℚ] w)).im = 0)
    (hpos : ∀ u ∈ H.holomorphic, u ≠ 0 →
      0 < (Complex.I * T (LinearMap.BilinMap.baseChange ℂ F u (WeightOne.CM.coefficientConjugation U u))).re) :
    Nonempty (CM.Polarization.WeightOnePolarization H) := by
  let b := Module.finBasis ℚ W
  have hB : ∀ i, (BilinearRational.CM.Construction.rationalBilinearCoordinate F b i).IsAlt := by
    intro i u
    change b.repr (F u u) i = 0
    rw [hF, map_zero, Finsupp.zero_apply]
  have hBi : ∀ i, ∀ u ∈ H.holomorphic, ∀ v ∈ H.holomorphic,
      (BilinearRational.CM.Construction.rationalBilinearCoordinate F b i).baseChange ℂ u v = 0 := by
    intro i u hu v hv
    rw [BilinearRational.CM.Construction.rationalBilinearCoordinate_baseChange, hiso u hu v hv, map_zero, Finsupp.zero_apply]
  have hBp : ∀ u ∈ H.holomorphic, u ≠ 0 →
      0 < (Complex.I * ∑ i, ((T ((1 : ℂ) ⊗ₜ[ℚ] b i)).re : ℂ) *
        (BilinearRational.CM.Construction.rationalBilinearCoordinate F b i).baseChange ℂ u (WeightOne.CM.coefficientConjugation U u)).re := by
    intro u hu hne
    rw [← BilinearRational.CM.Construction.rationalBilinear_real_functional_expansion F b T hT]
    exact hpos u hu hne
  obtain ⟨_, P, _⟩ := RationalPolarizationApproximation.CM.Construction.exists_rational_polarization_of_real_combination H
    (BilinearRational.CM.Construction.rationalBilinearCoordinate F b) hB hBi (fun i => (T ((1 : ℂ) ⊗ₜ[ℚ] b i)).re) hBp
  exact ⟨P⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolarizationFromRationalPairing.CM.Construction
