import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OverAlgebraIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.AffineDualProduct

/-! # Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.Coordinates

noncomputable section

/-! Actual products of affine fibers have tensor-product coordinates
over the full dual-number base. Their scheme automorphisms retain their
literal maps under the reconstructed algebra automorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [CommRing k] (X : Over (Spec (.of k))) [IsAffine X.left]

local instance affineProductCoordinates_tensorCommRing :
    CommRing (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)

def affineProductCoordinates :
    (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X ≅
      EtaleSplittingAt.EtaleSplitting.affineOver (DualNumber k) (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) := by
  let A := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X
  let a : X ≅ EtaleSplittingAt.EtaleSplitting.affineOver k A := HilbertConstruction.Affine.OverChartPoints.affineOverIso k X
  exact (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).mapIso a ≪≫
    (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso k A (DualNumber k)).symm

variable (e : (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X ≅
  (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X)

def affineProductCoordinateAutomorphism :=
  (affineProductCoordinates k X).symm ≪≫ e ≪≫ affineProductCoordinates k X

def affineProductAutomorphismAlgebra :=
  Affine.OverAlgebraIsomorphism.affineOverIsoAlgebraEquiv (DualNumber k)
    (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)
    (affineProductCoordinateAutomorphism k X e)

theorem affineProductAutomorphismAlgebra_spec :
    Spec.map (CommRingCat.ofHom (affineProductAutomorphismAlgebra k X e).toRingHom) =
      (affineProductCoordinateAutomorphism k X e).hom.left :=
  Affine.OverAlgebraIsomorphism.affineOverIsoAlgebraEquiv_spec (DualNumber k)
    (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)
    (affineProductCoordinateAutomorphism k X e)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.Coordinates
