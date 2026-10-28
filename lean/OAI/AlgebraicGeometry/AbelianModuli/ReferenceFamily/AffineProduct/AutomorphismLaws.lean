import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.Coordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OverAlgebraIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConjugateIsomorphismLaws

/-! # Automorphism Laws -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.AutomorphismLaws

noncomputable section

/-! Actual affine product automorphisms are recovered faithfully from
their base algebra automorphisms, with contravariant composition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k : Type) [CommRing k] (X : Over (Spec (.of k))) [IsAffine X.left]

local instance affineProductAutomorphismLaws_tensorCommRing :
    CommRing (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)

theorem affineProductCoordinateAutomorphism_trans
    (e f : (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X) :
    Coordinates.affineProductCoordinateAutomorphism k X (e ≪≫ f) =
      Coordinates.affineProductCoordinateAutomorphism k X e ≪≫ Coordinates.affineProductCoordinateAutomorphism k X f :=
  ConjugateIsomorphismLaws.conjugateIso_trans (Coordinates.affineProductCoordinates k X) e f

theorem affineProductAutomorphismAlgebra_trans
    (e f : (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X) :
    Coordinates.affineProductAutomorphismAlgebra k X (e ≪≫ f) =
      (Coordinates.affineProductAutomorphismAlgebra k X f).trans (Coordinates.affineProductAutomorphismAlgebra k X e) := by
  unfold Coordinates.affineProductAutomorphismAlgebra
  rw [affineProductCoordinateAutomorphism_trans]
  exact Affine.OverAlgebraIsomorphism.affineOverIsoAlgebraEquiv_trans (DualNumber k)
    (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)
    (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)
    (Coordinates.affineProductCoordinateAutomorphism k X e) (Coordinates.affineProductCoordinateAutomorphism k X f)

theorem affineProductAutomorphismAlgebra_refl :
    Coordinates.affineProductAutomorphismAlgebra k X (Iso.refl _) = AlgEquiv.refl := by
  unfold Coordinates.affineProductAutomorphismAlgebra Coordinates.affineProductCoordinateAutomorphism
  rw [ConjugateIsomorphismLaws.conjugateIso_refl]
  exact Affine.OverAlgebraIsomorphism.affineOverIsoAlgebraEquiv_refl (DualNumber k) (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)

theorem affineProductAutomorphismAlgebra_injective :
    Function.Injective (Coordinates.affineProductAutomorphismAlgebra k X) := by
  intro e f h
  have hc := Affine.OverAlgebraIsomorphism.affineOverIsoAlgebraEquiv_injective (DualNumber k)
    (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) h
  exact ConjugateIsomorphismLaws.conjugateIso_injective (Coordinates.affineProductCoordinates k X) hc

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.AutomorphismLaws
