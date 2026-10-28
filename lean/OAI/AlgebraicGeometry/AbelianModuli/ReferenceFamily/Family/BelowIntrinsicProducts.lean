import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.BelowTensorProducts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentBasePoint
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeTensorDiagramIso

/-! # Below Intrinsic Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.BelowIntrinsicProducts

noncomputable section

/-! On every affine subopen of one original chart, the actual
tangent-family pullbacks are naturally isomorphic to the constant products
of their actual fixed fibers. The isomorphism is built from the selected
linear lifts and the proved affine-coordinate comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R))) [Smooth X.hom]

def familyBelowNativeProductIso (W : X.left.affineOpens) (d : Derivation k R k) :
    Over.forget W ⋙ Affine.OpenDiagram.familyAffineOpenDiagram X ⋙ Over.pullback (TangentBasePoint.tangentBasePoint k R d) ≅
      Over.forget W ⋙ FixedFiber.AffineDiagram.fixedFiberAffineDiagram R k X ⋙ Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k) := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  let cSource := Functor.isoWhiskerLeft (Over.forget W) (FixedFiber.AffineDiagram.fixedFiberAffineCoordinates R (DualNumber k) X)
  let cProduct := Functor.isoWhiskerLeft (Over.forget W)
    (HilbertConstruction.SchemeTensorDiagramIso.algebraSchemeTensorDiagramIso k (DualNumber k) (FixedFiber.AffineDiagram.fixedFiberTensorAlgebras R k X))
  let cFiber := Functor.isoWhiskerLeft (Over.forget W)
    (Functor.isoWhiskerRight (FixedFiber.AffineDiagram.fixedFiberAffineCoordinates R k X).symm (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)))
  exact cSource ≪≫ (BelowTensorProducts.familyBelowTangentTensorIso k R X W d).symm ≪≫ cProduct ≪≫ cFiber

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.BelowIntrinsicProducts
