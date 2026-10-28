import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.ProEtaleCoefficients
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Cohomology

/-! # Cohomology Linearity -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.CohomologyLinearity.RationalProEtaleCoefficients

noncomputable section

/-! The actual integral-to-rational cohomology inclusion is linear over the p-adic integers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{0})

instance rationalIntegerModule (n : ℕ) : Module ℤ_[ℓ] (IntegralComparison.Cohomology.RationalEllAdicCohomology ℓ X n) :=
  Module.compHom _ (algebraMap ℤ_[ℓ] ℚ_[ℓ])

instance rationalIntegerTower (n : ℕ) :
    IsScalarTower ℤ_[ℓ] ℚ_[ℓ] (IntegralComparison.Cohomology.RationalEllAdicCohomology ℓ X n) where
  smul_assoc a b x := by
    change ((a : ℚ_[ℓ]) * b) • x = (a : ℚ_[ℓ]) • (b • x)
    exact mul_smul _ _ _

theorem integralInclusion_scalar (a : ℤ_[ℓ]) :
    AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.liftedEllAdicScalar ℓ X a ≫ ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X =
      ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X ≫ ProEtaleCoefficients.RationalProEtaleCoefficients.scalar ℓ X (a : ℚ_[ℓ]) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change ULift.{1} C(U.unop.left, ℤ_[ℓ]) at s
  change (ProEtaleCoefficients.RationalProEtaleCoefficients.coefficientInclusion ℓ U.unop.left (ULift.up (a • s.down)) :
    C(U.unop.left, IntegralComparison.Cohomology.Coeff.{0} ℓ)) = _
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  rfl

theorem cohomologyEquiv_inclusion (n : ℕ) (x : X.EllAdicCohomology ℓ n) :
    ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyEquiv ℓ X n (ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyInclusion ℓ X n x) =
      Sheaf.H.map (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X) n x :=
  (ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyEquiv ℓ X n).apply_symm_apply _

private theorem coefficient_scalar_cohomology (n : ℕ) (a : ℤ_[ℓ])
    (x : (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X).H n) :
    Sheaf.H.map (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X) n (Sheaf.H.map (AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.liftedEllAdicScalar ℓ X a) n x) =
      Sheaf.H.map (ProEtaleCoefficients.RationalProEtaleCoefficients.scalar ℓ X (a : ℚ_[ℓ])) n (Sheaf.H.map (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X) n x) := by
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, integralInclusion_scalar]

theorem cohomologyInclusion_smul (n : ℕ) (a : ℤ_[ℓ]) (x : X.EllAdicCohomology ℓ n) :
    ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyInclusion ℓ X n (a • x) = (a : ℚ_[ℓ]) • ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyInclusion ℓ X n x := by
  apply (ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyEquiv ℓ X n).injective
  rw [cohomologyEquiv_inclusion, ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyEquiv_smul, cohomologyEquiv_inclusion]
  change Sheaf.H.map (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X) n (Sheaf.H.map (AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.liftedEllAdicScalar ℓ X a) n x) = _
  exact coefficient_scalar_cohomology ℓ X n a x

def cohomologyInclusionLinear (n : ℕ) :
    X.EllAdicCohomology ℓ n →ₗ[ℤ_[ℓ]] IntegralComparison.Cohomology.RationalEllAdicCohomology ℓ X n where
  __ := ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyInclusion ℓ X n
  map_smul' := cohomologyInclusion_smul ℓ X n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.CohomologyLinearity.RationalProEtaleCoefficients
