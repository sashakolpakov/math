import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.RestrictionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenGroupRetractions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartGroupRetractionRestriction

/-! # Group Retraction Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.GroupRetractionRestriction

noncomputable section

/-! The original local family retractions commute with actual
restrictions to smaller affine opens, expressed in the selected
reference product charts on both opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver FixedFiber.AffineDiagram.fixedFiberTensorDiagram FixedFiber.AffineDiagram.fixedFiberTensorAlgebras
attribute [local implicit_reducible] Affine.OpenDiagram.familyAffineCoordinateFunctor HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor
attribute [local irreducible] CommonOpenProducts.familyCommonOpenProductEquiv
attribute [local irreducible] RestrictionCoordinates.familyReferenceRestrictionCoordinates CommonOpenGroupRetractions.familyCommonOpenGroupRetraction

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom]

theorem familyCommonOpenGroupRetraction_restrict {U V W : X.left.affineOpens}
    (t : U.1 ≤ V.1) (h : V.1 ≤ W.1) (d : Derivation ℂ R ℂ) :
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber (ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X V))
        (DualNumber (ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X U))
        (Dual.TensorMapCoordinates.dualTensorMapCoordinates (RestrictionCoordinates.familyReferenceRestrictionCoordinates ℂ R X t d)) ≫
      (CommonOpenGroupRetractions.familyCommonOpenGroupRetraction R X h d).val =
    (CommonOpenGroupRetractions.familyCommonOpenGroupRetraction R X (t.trans h) d).val := by
  let B := CommAlgCat.of ℂ (ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X V)
  let C := CommAlgCat.of ℂ (ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X U)
  let i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ TangentBasePoint.fixedFamilyFiber ℂ R X := FixedFiber.AffineDiagram.fixedFiberTensorInclusion R ℂ X V
  let j : EtaleSplittingAt.EtaleSplitting.affineOver ℂ C ⟶ TangentBasePoint.fixedFamilyFiber ℂ R X := FixedFiber.AffineDiagram.fixedFiberTensorInclusion R ℂ X U
  have : IsOpenImmersion i.left := FixedFiber.AffineDiagram.fixedFiberTensorInclusion_open R ℂ X V
  have : IsOpenImmersion j.left := FixedFiber.AffineDiagram.fixedFiberTensorInclusion_open R ℂ X U
  have hi : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B C (FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R ℂ X t) ≫ i = j :=
    FixedFiber.AffineDiagram.fixedFiberTensorInclusion_natural R ℂ X (homOfLE t)
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra ℂ R d
  let : Module R (DualNumber ℂ) := qD.toModule
  let : SMul R (DualNumber ℂ) := qD.toSMul
  have H := Product.ChartGroupRetractionRestriction.productChartGroupRetraction_restrict (TangentBasePoint.fixedFamilyFiber ℂ R X) B C i j
    (DualNumber ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X V) (DualNumber ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X U)
    (ProductRestrictionMaps.familyTangentTensorRestriction ℂ R X t d)
    (CommonOpenProducts.familyCommonOpenProductEquiv ℂ R X h d)
    (CommonOpenProducts.familyCommonOpenProductEquiv ℂ R X (le_refl V.1) d)
    (CommonOpenProducts.familyCommonOpenProductEquiv ℂ R X (t.trans h) d)
    (CommonOpenProducts.familyCommonOpenProductEquiv ℂ R X (le_refl U.1) d)
    (FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R ℂ X t)
    (CommonOpenProductNaturality.familyCommonOpenProductEquiv_restrict ℂ R X t h d) hi
    (BaseTangentTensor.baseTangentScalarReduction ℂ R (AffineTangentLifts.familyAffineRing R X V) d)
    (BaseTangentTensor.baseTangentScalarReduction ℂ R (AffineTangentLifts.familyAffineRing R X U) d)
    (CommonOpenProducts.familyCommonOpenProductEquiv_reduction ℂ R X h d)
    (CommonOpenProducts.familyCommonOpenProductEquiv_reduction ℂ R X (le_refl V.1) d)
    (CommonOpenProducts.familyCommonOpenProductEquiv_reduction ℂ R X (t.trans h) d)
    (CommonOpenProducts.familyCommonOpenProductEquiv_reduction ℂ R X (le_refl U.1) d)
  simpa only [RestrictionCoordinates.familyReferenceRestrictionCoordinates, CommonOpenGroupRetractions.familyCommonOpenGroupRetraction] using H

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.GroupRetractionRestriction
