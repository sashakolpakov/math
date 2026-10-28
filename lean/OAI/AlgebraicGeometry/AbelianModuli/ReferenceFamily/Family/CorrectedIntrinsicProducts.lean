import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedSchemeSquare
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentBasePoint
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeTensorDiagramIso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.ProductDiagramCoordinates

/-! # Corrected Intrinsic Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedIntrinsicProducts

noncomputable section

/-! Corrected affine products transported to the actual tangent
family and the constant product of the actual original fixed fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R))) [Smooth X.hom]

def familyBelowCorrectedNativeIso (W : X.left.affineOpens) (d : Derivation k R k)
    (a : Derivation k (k ⊗[R] AffineTangentLifts.familyAffineRing R X W) (k ⊗[R] AffineTangentLifts.familyAffineRing R X W)) :
    Over.forget W ⋙ Affine.OpenDiagram.familyAffineOpenDiagram X ⋙ Over.pullback (TangentBasePoint.tangentBasePoint k R d) ≅
      Over.forget W ⋙ FixedFiber.AffineDiagram.fixedFiberAffineDiagram R k X ⋙ Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k) := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  let cSource := Functor.isoWhiskerLeft (Over.forget W) (ProductDiagramCoordinates.familyTangentDiagramCoordinates k R X d)
  let cTarget := Functor.isoWhiskerLeft (Over.forget W) (ProductDiagramCoordinates.familyConstantDiagramCoordinates k R X)
  exact cSource ≪≫ (CorrectedSchemeSquare.familyBelowCorrectedTensorIso k R X W d a).symm ≪≫ cTarget

attribute [local irreducible] familyBelowCorrectedNativeIso
attribute [local implicit_reducible] Affine.OpenDiagram.familyAffineOpenDiagram FixedFiber.AffineDiagram.fixedFiberAffineDiagram

def familyCorrectedNativeProduct {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (d : Derivation k R k)
    (a : Derivation k (k ⊗[R] AffineTangentLifts.familyAffineRing R X W) (k ⊗[R] AffineTangentLifts.familyAffineRing R X W)) :
    (Over.pullback (TangentBasePoint.tangentBasePoint k R d)).obj ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj V) ≅
      (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).obj ((FixedFiber.AffineDiagram.fixedFiberAffineDiagram R k X).obj V) :=
  (familyBelowCorrectedNativeIso k R X W d a).app (Over.mk (homOfLE h))

theorem familyCorrectedNativeProduct_restrict {U V W : X.left.affineOpens}
    (t : U.1 ≤ V.1) (h : V.1 ≤ W.1) (d : Derivation k R k)
    (a : Derivation k (k ⊗[R] AffineTangentLifts.familyAffineRing R X W) (k ⊗[R] AffineTangentLifts.familyAffineRing R X W)) :
    (Over.pullback (TangentBasePoint.tangentBasePoint k R d)).map (Affine.OpenDiagram.familyOpenMap X t) ≫
        (familyCorrectedNativeProduct k R X h d a).hom =
      (familyCorrectedNativeProduct k R X (t.trans h) d a).hom ≫
        (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).map ((FixedFiber.AffineDiagram.fixedFiberAffineDiagram R k X).map (homOfLE t)) := by
  let p : Over W := Over.mk (show U ⟶ W from homOfLE (t.trans h))
  let q : Over W := Over.mk (show V ⟶ W from homOfLE h)
  let f : p ⟶ q := Over.homMk (homOfLE t) (Subsingleton.elim _ _)
  exact (familyBelowCorrectedNativeIso k R X W d a).hom.naturality f

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedIntrinsicProducts
