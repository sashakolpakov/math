import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.Coordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.AlgebraAutomorphismNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IsoNaturalitySquares
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateDiagramIso

/-! # Coordinate Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.CoordinateNaturality

noncomputable section

/-! The actual tensor coordinates of affine products commute with
the coefficient maps of the original affine fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver Affine.AlgebraAutomorphismNaturality.affineOverAlgHom Smooth.AffineDualProduct.dualBaseProjection

variable (k : Type) [CommRing k] {X Y : Over (Spec (.of k))} [IsAffine X.left] [IsAffine Y.left]

local instance affineProductCoordinateNaturality_sourceCommRing :
    CommRing (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)

local instance affineProductCoordinateNaturality_targetCommRing :
    CommRing (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y)

theorem affineProductCoordinates_natural (f : X ⟶ Y) :
    (Coordinates.affineProductCoordinates k X).hom ≫
        Affine.AlgebraAutomorphismNaturality.affineOverAlgHom (DualNumber k) (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y)
          (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)
          (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) (HilbertConstruction.Affine.OverMorphisms.affineOverMap k f)) =
      (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).map f ≫ (Coordinates.affineProductCoordinates k Y).hom := by
  let T := Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)
  let A := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X
  let B := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y
  let ex : X ≅ EtaleSplittingAt.EtaleSplitting.affineOver k A := HilbertConstruction.Affine.OverChartPoints.affineOverIso k X
  let ey : Y ≅ EtaleSplittingAt.EtaleSplitting.affineOver k B := HilbertConstruction.Affine.OverChartPoints.affineOverIso k Y
  let q := HilbertConstruction.Affine.OverMorphisms.affineOverMap k f
  let M := Affine.AlgebraAutomorphismNaturality.affineOverAlgHom (DualNumber k) (DualNumber k ⊗[k] B) (DualNumber k ⊗[k] A)
    (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q)
  have hb : (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso k A (DualNumber k)).hom ≫ T.map (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B A q) =
      M ≫ (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso k B (DualNumber k)).hom :=
    Affine.AlgebraAutomorphismNaturality.affineBaseChangeIso_natural k B A (DualNumber k) q
  have hi := IsoNaturalitySquares.iso_inverse_square (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso k A (DualNumber k))
    (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso k B (DualNumber k)) M (T.map (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B A q)) hb
  have hn : f ≫ ey.hom =
      ex.hom ≫ Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B A q := HilbertConstruction.Affine.CoordinateDiagramIso.affineOverIso_natural k f
  calc
    (Coordinates.affineProductCoordinates k X).hom ≫ M =
        (T.map ex.hom ≫ (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso k A (DualNumber k)).inv) ≫ M := rfl
    _ = T.map ex.hom ≫
        ((EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso k A (DualNumber k)).inv ≫ M) := Category.assoc _ _ _
    _ = T.map ex.hom ≫
        (T.map (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B A q) ≫ (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso k B (DualNumber k)).inv) := by rw [hi]
    _ = T.map (ex.hom ≫ Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B A q) ≫
        (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso k B (DualNumber k)).inv := by rw [T.map_comp, Category.assoc]
    _ = T.map (f ≫ ey.hom) ≫
        (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso k B (DualNumber k)).inv := by rw [← hn]
    _ = T.map f ≫ (Coordinates.affineProductCoordinates k Y).hom := by
      rw [T.map_comp, Category.assoc]
      rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.CoordinateNaturality
