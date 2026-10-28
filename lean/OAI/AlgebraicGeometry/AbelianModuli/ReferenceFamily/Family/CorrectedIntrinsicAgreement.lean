import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedIntrinsicProducts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedProductAgreement

/-! # Corrected Intrinsic Agreement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedIntrinsicAgreement

noncomputable section

/-! Corrected actual family products agree on common affine opens.
The comparison uses the same native affine-coordinate isomorphisms for
both products. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    (U : X.left.AffineOpenCover) (d : Derivation ℂ R ℂ)
    (a : FamilyTangent.Primitives.fixedFamilyDerivationGauges R X U) (ha : FamilyTangent.Primitives.IsFamilyTangentDerivationPrimitive R X U d a)

attribute [local irreducible] CorrectedProducts.familyCorrectedProductEquiv
attribute [local irreducible] FixedFiber.AffineDiagram.fixedFiberAffineCoordinates HilbertConstruction.SchemeTensorDiagramIso.algebraSchemeTensorDiagramIso
attribute [local irreducible] EtaleSplittingAt.EtaleSplitting.affineAlgIso
attribute [local irreducible] ProductDiagramCoordinates.familyTangentDiagramCoordinates ProductDiagramCoordinates.familyConstantDiagramCoordinates
attribute [local implicit_reducible] FixedFiber.AffineDiagram.fixedFiberAffineDiagram TangentBasePoint.tangentBasePoint BaseTangentTensorLifts.baseTangentDualAlgebra
attribute [local implicit_reducible] FixedFiber.AffineDiagram.fixedFiberTensorDiagram FixedFiber.AffineDiagram.fixedFiberTensorAlgebras Affine.OpenDiagram.familyAffineOpenDiagram
attribute [local implicit_reducible] HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor
attribute [local implicit_reducible] Affine.OpenDiagram.familyAffineCoordinateFunctor HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor EtaleSplittingAt.EtaleSplitting.affineOver

include ha in
theorem familyCorrectedNativeProduct_common_eq (V : X.left.affineOpens) (i j : U.I₀)
    (hi : V.1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U i).1)
    (hj : V.1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U j).1) :
    CorrectedIntrinsicProducts.familyCorrectedNativeProduct ℂ R X hi d (a i) = CorrectedIntrinsicProducts.familyCorrectedNativeProduct ℂ R X hj d (a j) := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra ℂ R d
  let : Module R (DualNumber ℂ) := qD.toModule
  let : SMul R (DualNumber ℂ) := qD.toSMul
  have he := CorrectedProductAgreement.familyCorrectedProductEquiv_common_eq R X U d a ha V i j hi hj
  apply Iso.ext
  change (ProductDiagramCoordinates.familyTangentDiagramCoordinates ℂ R X d).hom.app V ≫
      (EtaleSplittingAt.EtaleSplitting.affineAlgIso (DualNumber ℂ) (DualNumber ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X V)
        (CorrectedProducts.familyCorrectedProductEquiv ℂ R X hi d (a i))).inv ≫
      (ProductDiagramCoordinates.familyConstantDiagramCoordinates ℂ R X).hom.app V =
    (ProductDiagramCoordinates.familyTangentDiagramCoordinates ℂ R X d).hom.app V ≫
      (EtaleSplittingAt.EtaleSplitting.affineAlgIso (DualNumber ℂ) (DualNumber ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X V)
        (CorrectedProducts.familyCorrectedProductEquiv ℂ R X hj d (a j))).inv ≫
      (ProductDiagramCoordinates.familyConstantDiagramCoordinates ℂ R X).hom.app V
  rw [he]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedIntrinsicAgreement
