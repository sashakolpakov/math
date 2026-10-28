import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.BelowIntrinsicProducts

/-! # Product Diagram Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.ProductDiagramCoordinates

noncomputable section

/-! Coordinate comparisons with the exact tangent and constant
family diagrams exposed in their types. This retains the original base
maps when manipulating components of the product isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R)))

def familyTangentDiagramCoordinates (d : Derivation k R k) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    Affine.OpenDiagram.familyAffineOpenDiagram X ⋙ Over.pullback (TangentBasePoint.tangentBasePoint k R d) ≅
      FixedFiber.AffineDiagram.fixedFiberTensorDiagram R (DualNumber k) X := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  exact FixedFiber.AffineDiagram.fixedFiberAffineCoordinates R (DualNumber k) X

def familyConstantDiagramCoordinates :
    HilbertConstruction.AlgebraSchemeDiagrams.algebraSchemeDiagram (DualNumber k)
      (FixedFiber.AffineDiagram.fixedFiberTensorAlgebras R k X ⋙ HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor k (DualNumber k)) ≅
      FixedFiber.AffineDiagram.fixedFiberAffineDiagram R k X ⋙ Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k) :=
  HilbertConstruction.SchemeTensorDiagramIso.algebraSchemeTensorDiagramIso k (DualNumber k) (FixedFiber.AffineDiagram.fixedFiberTensorAlgebras R k X) ≪≫
    Functor.isoWhiskerRight (FixedFiber.AffineDiagram.fixedFiberAffineCoordinates R k X).symm (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.ProductDiagramCoordinates
