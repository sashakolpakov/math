import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CoefficientAffineLift
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartCoefficientConormal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent

/-! # Chart Coefficient Derivative -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChartCoefficientDerivative

noncomputable section

/-! An actual affine open chart identifies the native tangent space
linearly with coefficient derivations, and the two constructions give
the exact same scheme-valued dual-number lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (B : CommAlgCat ℂ) [IsDomain B] [Algebra.Smooth ℂ B]
    [Algebra B ℂ] [IsScalarTower ℂ B ℂ]
    (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ X) [IsOpenImmersion i.left]

local instance nativeChartCoefficient_open :
    IsOpenImmersion (show Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X from i).left :=
  inferInstanceAs (IsOpenImmersion i.left)

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelB" => (Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ)

def nativeChartCoefficientDerivative : ModelX ≃ₗ[ℂ] Derivation ℂ B ℂ :=
  (LinearEquiv.ofBijective
    (mfderiv 𝓘(ℂ, ModelB) 𝓘(ℂ, ModelX)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i) (IsScalarTower.toAlgHom ℂ B ℂ)).toLinearMap
    (ComplexPoints.Analytic.AffineOpenDifferential.mfderiv_affinePointMap_bijective B i (IsScalarTower.toAlgHom ℂ B ℂ))).symm.trans
      (CoefficientPointDerivations.nativeAffineCoefficientDerivationEquiv B)

theorem nativeChartCoefficientDerivative_lift (v : ModelX) :
    ((Affine.ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B ℂ X i).symm (nativeChartCoefficientDerivative X B i v)).val =
      (SchemeDualTangent.nativeSchemeTangentDualEquiv X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i (IsScalarTower.toAlgHom ℂ B ℂ)) v).val := by
  let d := LinearEquiv.ofBijective
    (mfderiv 𝓘(ℂ, ModelB) 𝓘(ℂ, ModelX)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i) (IsScalarTower.toAlgHom ℂ B ℂ)).toLinearMap
    (ComplexPoints.Analytic.AffineOpenDifferential.mfderiv_affinePointMap_bijective B i (IsScalarTower.toAlgHom ℂ B ℂ))
  let w := d.symm v
  have hv : mfderiv 𝓘(ℂ, ModelB) 𝓘(ℂ, ModelX)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i) (IsScalarTower.toAlgHom ℂ B ℂ) w = v := d.apply_symm_apply v
  change ((Affine.DualLiftConormal.affineDualLiftDerivationEquiv ℂ B ℂ).symm (CoefficientPointDerivations.nativeAffineCoefficientDerivationEquiv B w)).val ≫ i = _
  rw [CoefficientAffineLift.nativeCoefficientAffineLift_eq]
  have hn := SchemeDualTangent.nativeSchemeTangentDual_mfderiv X B i (IsScalarTower.toAlgHom ℂ B ℂ) w
  rw [hv] at hn
  exact hn.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChartCoefficientDerivative
