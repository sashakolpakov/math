import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantConormalGroupLifts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConormalLift
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationConormalLinearity

/-! # Constant Conormal Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConstantConormalLift

noncomputable section

/-! A constant conormal derivation on an actual affine group chart
is the derivation of the original infinitesimal group translation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral G.left] [Smooth G.hom] [GrpObj G]
    (B : CommAlgCat ℂ) (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) [IsOpenImmersion i.left]
    (l : Constructed.IdentityConormal.constructedIdentityConormal ℂ G →ₗ[ℂ] ℂ)

def affineConstantConormalLift :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber B) ⟶ G // Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ B ≫ f =
      ChartCoefficientConormal.affineChartCoefficientPoint ℂ B B G i} :=
  let c := IntrinsicCoefficientPoint.openAffineLiftReference ℂ B G (ChartCoefficientConormal.affineChartCoefficientPoint ℂ B B G i)
  let f := ConstantConormalGroupLifts.constantTranslatedConormalLift G B l c
  ⟨f.val, f.property.trans (IntrinsicCoefficientPoint.openAffineLiftReference_reduction ℂ B G (ChartCoefficientConormal.affineChartCoefficientPoint ℂ B B G i))⟩

theorem affineConstantConormalLift_coordinates :
    PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B i
      (ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B B G i (affineConstantConormalLift G B i l)) =
        ConormalUnitLogCoordinates.coefficientCovector B l := by
  have h := ConormalLift.affineChartConormal_originalLift ℂ B B G i (affineConstantConormalLift G B i l)
  exact h.trans (ConstantConormalGroupLifts.constantTranslatedConormalLift_coordinates G B l
    (IntrinsicCoefficientPoint.openAffineLiftReference ℂ B G (ChartCoefficientConormal.affineChartCoefficientPoint ℂ B B G i)))

theorem affineConstantConormalLift_derivation :
    ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B B G i (affineConstantConormalLift G B i l) =
      (PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B i).symm (ConormalUnitLogCoordinates.coefficientCovector B l) :=
  (PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B i).eq_symm_apply.mpr (affineConstantConormalLift_coordinates G B i l)

omit l [IsOpenImmersion i.left] in
theorem affineConstantConormalLift_native
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension G.hom) → ℂ) :
    (affineConstantConormalLift G B i (Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G v)).val =
      (AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber ℂ) (DualNumber B) (Dual.NumberCoefficients.dualNumberAlgMap (Algebra.ofId ℂ B)) ≫
        (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v).val) *
          IntrinsicCoefficientPoint.openAffineLiftReference ℂ B G (ChartCoefficientConormal.affineChartCoefficientPoint ℂ B B G i) :=
  congrArg (fun f => f * IntrinsicCoefficientPoint.openAffineLiftReference ℂ B G (ChartCoefficientConormal.affineChartCoefficientPoint ℂ B B G i))
    (ConstantConormalGroupLifts.constantIdentityConormalLift_native G B v)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConstantConormalLift
