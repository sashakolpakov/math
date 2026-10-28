import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.CohomologyIsoNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.ScalarExtension

/-! # Algebraic Rational -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicRational.RationalProEtaleCoefficients

noncomputable section

/-! The original algebraic-coefficient integral H¹ agrees with scalar extension of the actual rational H¹, naturally for scheme isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius

variable (ℓ : ℕ) [Fact ℓ.Prime]

abbrev AlgebraicRationalH1 (X : Scheme.{0}) :=
  AlgebraicClosure ℚ_[ℓ] ⊗[ℚ_[ℓ]] IntegralComparison.Cohomology.RationalEllAdicCohomology ℓ X 1

def algebraicH1Equiv (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] :
    AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.EllAdicH1AlgebraicCoefficients ℓ X ≃ₗ[AlgebraicClosure ℚ_[ℓ]] AlgebraicRationalH1 ℓ X :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ_[ℓ] ℚ_[ℓ]
    (AlgebraicClosure ℚ_[ℓ]) (AlgebraicClosure ℚ_[ℓ]) (X.EllAdicCohomology ℓ 1)).symm.trans
      ((Rational.ScalarExtension.RationalProEtaleCoefficients.rationalH1Equiv ℓ X).baseChange ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) _ _)

theorem algebraicH1Equiv_tmul (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X]
    (a : AlgebraicClosure ℚ_[ℓ]) (x : X.EllAdicCohomology ℓ 1) :
    algebraicH1Equiv ℓ X (a ⊗ₜ[ℤ_[ℓ]] x) = a ⊗ₜ[ℚ_[ℓ]] Rational.ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyInclusion ℓ X 1 x := by
  rw [algebraicH1Equiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.baseChange_tmul,
    Rational.ScalarExtension.RationalProEtaleCoefficients.rationalH1Equiv_tmul, one_smul]

theorem algebraicH1Equiv_pullback {X Y : Scheme.{0}} (e : X ≅ Y)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    (algebraicH1Equiv ℓ X).toLinearMap.comp (AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ e.hom) =
      (((IntegralComparison.Etale.Frobenius.cohomologyPullback ℓ e 1).restrictScalars ℚ_[ℓ]).toLinearMap.baseChange
        (AlgebraicClosure ℚ_[ℓ])).comp (algebraicH1Equiv ℓ Y).toLinearMap := by
  ext x
  change algebraicH1Equiv ℓ X (1 ⊗ₜ[ℤ_[ℓ]] AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.integralEllAdicPullback ℓ e.hom 1 x) =
    (((IntegralComparison.Etale.Frobenius.cohomologyPullback ℓ e 1).restrictScalars ℚ_[ℓ]).toLinearMap.baseChange
      (AlgebraicClosure ℚ_[ℓ])) (algebraicH1Equiv ℓ Y (1 ⊗ₜ[ℤ_[ℓ]] x))
  rw [algebraicH1Equiv_tmul, algebraicH1Equiv_tmul, LinearMap.baseChange_tmul]
  exact congrArg (fun y => (1 : AlgebraicClosure ℚ_[ℓ]) ⊗ₜ[ℚ_[ℓ]] y)
    (Rational.CohomologyIsoNaturality.RationalProEtaleCoefficients.cohomologyInclusion_pullback ℓ e 1 x)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicRational.RationalProEtaleCoefficients
