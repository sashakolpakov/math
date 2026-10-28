import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.Coordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OverAlgebraIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.AutomorphismFiberIdentity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FunctorFixedAutomorphisms

/-! # Algebra Automorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.AlgebraAutomorphisms

noncomputable section

/-! Actual tensor algebra automorphisms construct automorphisms of the
original affine scheme product. Reconstruction returns their exact algebra
maps, and preserving reduction fixes the actual scheme special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k : Type) [Field k] (X : Over (Spec (.of k))) [IsAffine X.left]

local instance affineProductAlgebraAutomorphisms_tensorCommRing :
    CommRing (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)

variable (e : (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) ≃ₐ[DualNumber k]
  (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X))

def affineProductAlgebraAutomorphism :
    (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X :=
  Coordinates.affineProductCoordinates k X ≪≫
    EtaleSplittingAt.EtaleSplitting.affineAlgIso (DualNumber k) (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) e ≪≫
      (Coordinates.affineProductCoordinates k X).symm

theorem affineProductAlgebraAutomorphism_coordinates :
    Coordinates.affineProductCoordinateAutomorphism k X (affineProductAlgebraAutomorphism k X e) =
      EtaleSplittingAt.EtaleSplitting.affineAlgIso (DualNumber k) (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) e := by
  apply Iso.ext
  simp only [Coordinates.affineProductCoordinateAutomorphism, affineProductAlgebraAutomorphism,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

theorem affineProductAlgebraAutomorphism_algebra :
    Coordinates.affineProductAutomorphismAlgebra k X (affineProductAlgebraAutomorphism k X e) = e := by
  unfold Coordinates.affineProductAutomorphismAlgebra
  rw [affineProductAlgebraAutomorphism_coordinates]
  exact Affine.OverAlgebraIsomorphism.affineOverIsoAlgebraEquiv_affineAlgIso (DualNumber k)
    (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) e

theorem affineProductAlgebraAutomorphism_fiberIdentity
    (he : ∀ u, Dual.TensorReduction.dualTensorReduction k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) (e u) =
      Dual.TensorReduction.dualTensorReduction k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) u) :
    (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (affineProductAlgebraAutomorphism k X e).hom = 𝟙 _ :=
  FunctorFixedAutomorphisms.functor_map_conjugate_identity (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)) (Coordinates.affineProductCoordinates k X).symm
    (EtaleSplittingAt.EtaleSplitting.affineAlgIso (DualNumber k) (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) e)
    (Tensor.AutomorphismFiberIdentity.tensorAlgebraAutomorphism_fiberIdentity k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) e he)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.AlgebraAutomorphisms
