import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductRetractionConormal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenProducts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.AffineCoefficient

/-! # Common Open Group Retractions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenGroupRetractions

noncomputable section

/-! The family's original product charts give actual retractions into
the fixed group. Their conormal discrepancies are the original affine
family tangent differences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver FixedFiber.AffineDiagram.fixedFiberTensorDiagram FixedFiber.AffineDiagram.fixedFiberTensorAlgebras
attribute [local implicit_reducible] Affine.OpenDiagram.familyAffineCoordinateFunctor HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom]

def familyCommonOpenGroupRetraction {V W : X.left.affineOpens}
    (h : V.1 ≤ W.1) (d : Derivation ℂ R ℂ) :
    {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber (ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X V)) ⟶ TangentBasePoint.fixedFamilyFiber ℂ R X //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ (ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X V) ≫ u =
        Affine.ChartCoefficientConormal.affineChartCoefficientPoint ℂ (ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X V)
          (ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X V) (TangentBasePoint.fixedFamilyFiber ℂ R X)
          (FixedFiber.AffineDiagram.fixedFiberTensorInclusion R ℂ X V)} := by
  let B := CommAlgCat.of ℂ (ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X V)
  let i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ TangentBasePoint.fixedFamilyFiber ℂ R X := FixedFiber.AffineDiagram.fixedFiberTensorInclusion R ℂ X V
  have : IsOpenImmersion i.left := FixedFiber.AffineDiagram.fixedFiberTensorInclusion_open R ℂ X V
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra ℂ R d
  let : Module R (DualNumber ℂ) := qD.toModule
  let : SMul R (DualNumber ℂ) := qD.toSMul
  exact Dual.ProductRetractionConormal.productChartGroupRetraction (TangentBasePoint.fixedFamilyFiber ℂ R X)
    B i
    (DualNumber ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X V)
    (BaseTangentTensor.baseTangentScalarReduction ℂ R (AffineTangentLifts.familyAffineRing R X V) d)
    (CommonOpenProducts.familyCommonOpenProductEquiv ℂ R X h d)
    (CommonOpenProducts.familyCommonOpenProductEquiv ℂ R X (le_refl V.1) d)
    (CommonOpenProducts.familyCommonOpenProductEquiv_reduction ℂ R X h d)
    (CommonOpenProducts.familyCommonOpenProductEquiv_reduction ℂ R X (le_refl V.1) d)

variable [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)]

theorem familyCommonOpenGroupRetraction_conormal {V W Z : X.left.affineOpens}
    (h : V.1 ≤ W.1) (j : V.1 ≤ Z.1) (d : Derivation ℂ R ℂ) :
    Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)
        (ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X V) (familyCommonOpenGroupRetraction R X j d).val
        ⟨(familyCommonOpenGroupRetraction R X h d).val,
          (familyCommonOpenGroupRetraction R X h d).property.trans
            (familyCommonOpenGroupRetraction R X j d).property.symm⟩ =
      FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv R X V (CommonOpenTangentDifferences.familyCommonOpenTangentDifference ℂ R X h j d) := by
  let B := CommAlgCat.of ℂ (ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X V)
  let i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ TangentBasePoint.fixedFamilyFiber ℂ R X := FixedFiber.AffineDiagram.fixedFiberTensorInclusion R ℂ X V
  have : IsOpenImmersion i.left := FixedFiber.AffineDiagram.fixedFiberTensorInclusion_open R ℂ X V
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra ℂ R d
  let : Module R (DualNumber ℂ) := qD.toModule
  let : SMul R (DualNumber ℂ) := qD.toSMul
  have hc := Dual.ProductRetractionConormal.productChartGroupRetraction_conormal (TangentBasePoint.fixedFamilyFiber ℂ R X)
    B i
    (DualNumber ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X V)
    (BaseTangentTensor.baseTangentScalarReduction ℂ R (AffineTangentLifts.familyAffineRing R X V) d)
    (CommonOpenProducts.familyCommonOpenProductEquiv ℂ R X h d)
    (CommonOpenProducts.familyCommonOpenProductEquiv ℂ R X (le_refl V.1) d)
    (CommonOpenProducts.familyCommonOpenProductEquiv_reduction ℂ R X h d)
    (CommonOpenProducts.familyCommonOpenProductEquiv_reduction ℂ R X (le_refl V.1) d)
    (CommonOpenProducts.familyCommonOpenProductEquiv ℂ R X j d)
    (CommonOpenProducts.familyCommonOpenProductEquiv_reduction ℂ R X j d)
  have hd := congrArg (FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv R X V) (CommonOpenProducts.familyCommonOpenProduct_transition ℂ R X h j d)
  exact hc.trans hd

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenGroupRetractions
