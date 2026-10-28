import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChartCoefficientDerivative
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.IntrinsicCoefficientPoint
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PointChartCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.IdentityConormal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConormalLiftInverseFormulas

/-! # Identity Conormal Linear -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear

noncomputable section

/-! The constructed identity conormal identifies linearly with the
native tangent space. Its inverse gives the exact original group lift,
including translation by any reference map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver LieRanks.dualNumberTest PELModuli.IntegralModel.Section.ConormalMaps.SectionConormal.module

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] [GrpObj X]

local notation "B₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.IdentityConormal.constructedIdentityAlgebra ℂ X
local notation "i₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PointChartCoordinates.affinePointChartInclusion ℂ X 1 (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.IdentityConormal.selectedAffineIdentityChart ℂ X)
local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)

local instance nativeIdentityAlgebra_domain : IsDomain B₀ :=
  Affine.PointChartCoordinates.affinePointChartAlgebra_isDomain ℂ X 1 (Constructed.IdentityConormal.selectedAffineIdentityChart ℂ X)

local instance nativeIdentityAlgebra_section : Algebra B₀ ℂ :=
  (Constructed.IdentityConormal.constructedIdentityAugmentation ℂ X).toRingHom.toAlgebra

local instance nativeIdentityAlgebra_sectionTower : IsScalarTower ℂ B₀ ℂ :=
  IsScalarTower.of_algebraMap_eq (fun r => (Constructed.IdentityConormal.constructedIdentityAugmentation ℂ X).commutes r |>.symm)

omit [IsIntegral X.left] [Smooth X.hom] in
theorem nativeIdentityAugmentation_fac : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B₀ ℂ (IsScalarTower.toAlgHom ℂ B₀ ℂ) ≫ i₀ = 1 :=
  Affine.PointChartCoordinates.affinePointChartAugmentation_fac ℂ X 1 (Constructed.IdentityConormal.selectedAffineIdentityChart ℂ X)

def nativeIdentityConormalLinear : ModelX ≃ₗ[ℂ] (Constructed.IdentityConormal.constructedIdentityConormal ℂ X →ₗ[ℂ] ℂ) :=
  (ChartCoefficientDerivative.nativeChartCoefficientDerivative X B₀ i₀).trans (PELModuli.IntegralModel.Section.ConormalDerivations.SectionConormal.derivationConormalEquiv ℂ B₀ ℂ)

theorem nativeIdentityConormalLinear_inverse (v : ModelX) (c : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ X) :
    ((GroupCoefficientConormal.groupCoefficientConormalEquiv ℂ B₀ ℂ i₀
      (nativeIdentityAugmentation_fac X) c).symm
        (nativeIdentityConormalLinear X v)).val =
      (show EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ X from (SchemeDualTangent.nativeSchemeTangentDualEquiv X 1 v).val) * c := by
  change ((GroupCoefficientConormal.groupCoefficientConormalEquiv ℂ B₀ ℂ i₀
      (nativeIdentityAugmentation_fac X) c).symm
        (PELModuli.IntegralModel.Section.ConormalDerivations.SectionConormal.derivationConormalEquiv ℂ B₀ ℂ (ChartCoefficientDerivative.nativeChartCoefficientDerivative X B₀ i₀ v))).val = _
  rw [ConormalLiftInverseFormulas.groupCoefficientConormalEquiv_symm_derivation]
  have hn : ((Affine.DualLiftConormal.affineDualLiftDerivationEquiv ℂ B₀ ℂ).symm (ChartCoefficientDerivative.nativeChartCoefficientDerivative X B₀ i₀ v)).val ≫ i₀ =
      (SchemeDualTangent.nativeSchemeTangentDualEquiv X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B₀ i₀ (IsScalarTower.toAlgHom ℂ B₀ ℂ)) v).val :=
    ChartCoefficientDerivative.nativeChartCoefficientDerivative_lift X B₀ i₀ v
  have hp := Affine.IntrinsicCoefficientPoint.nativeAffineCoefficientPoint_one X B₀ i₀ (IsScalarTower.toAlgHom ℂ B₀ ℂ)
    (nativeIdentityAugmentation_fac X)
  exact congrArg (fun f : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ X => f * c)
    (hn.trans (congrArg (fun p => (SchemeDualTangent.nativeSchemeTangentDualEquiv X p v).val) hp))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear
