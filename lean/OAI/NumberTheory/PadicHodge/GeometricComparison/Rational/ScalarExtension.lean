import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.Denominators
import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.Kernel
import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.CohomologyLinearity
import OAI.NumberTheory.PadicHodge.GeometricComparison.ContinuousDenominators

/-! # Scalar Extension -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.ScalarExtension.RationalProEtaleCoefficients

noncomputable section

/-! Actual degree-one rational pro-étale cohomology is scalar extension of actual integral cohomology on a quasi-compact quasi-separated scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X]

instance cohomologyInclusion_localized :
    IsLocalizedModule.Away (ℓ : ℤ_[ℓ]) (CohomologyLinearity.RationalProEtaleCoefficients.cohomologyInclusionLinear ℓ X 1) := by
  apply IsLocalizedModule.Away.mk_of_addCommGroup
  · rw [← (Algebra.lsmul ℤ_[ℓ] (A := ℚ_[ℓ]) ℤ_[ℓ]
      (IntegralComparison.Cohomology.RationalEllAdicCohomology ℓ X 1)).commutes]
    exact (IsLocalization.Away.algebraMap_isUnit (ℓ : ℤ_[ℓ]) (S := ℚ_[ℓ])).map _
  · intro x
    obtain ⟨N, y, hy⟩ := Denominators.RationalProEtaleCoefficients.rationalH1_denominator ℓ X x
    refine ⟨N, y, ?_⟩
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact hy.symm
  · intro x hx
    obtain ⟨N, hN⟩ := Kernel.RationalProEtaleCoefficients.cohomologyInclusion_kernel_torsion ℓ X x hx
    refine ⟨N, ?_⟩
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact hN

def rationalH1Equiv :
    (ℚ_[ℓ] ⊗[ℤ_[ℓ]] X.EllAdicCohomology ℓ 1) ≃ₗ[ℚ_[ℓ]] IntegralComparison.Cohomology.RationalEllAdicCohomology ℓ X 1 :=
  (IsLocalizedModule.isBaseChange (Submonoid.powers (ℓ : ℤ_[ℓ])) ℚ_[ℓ]
    (CohomologyLinearity.RationalProEtaleCoefficients.cohomologyInclusionLinear ℓ X 1)).equiv

theorem rationalH1Equiv_tmul (a : ℚ_[ℓ]) (x : X.EllAdicCohomology ℓ 1) :
    rationalH1Equiv ℓ X (a ⊗ₜ[ℤ_[ℓ]] x) = a • ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyInclusion ℓ X 1 x :=
  IsBaseChange.equiv_tmul _ _ _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.ScalarExtension.RationalProEtaleCoefficients
