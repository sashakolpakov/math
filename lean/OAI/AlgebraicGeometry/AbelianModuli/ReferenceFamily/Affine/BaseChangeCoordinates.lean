import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.AlgebraAutomorphismNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IsoNaturalitySquares
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateDiagramIso

/-! # Base Change Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.BaseChangeCoordinates

noncomputable section

/-! Tensor coordinates identify the actual base changes of arbitrary
affine families, naturally in the original scheme maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver AlgebraAutomorphismNaturality.affineOverAlgHom

variable (R T : Type) [CommRing R] [CommRing T] [Algebra R T]

local instance baseChangeCoordinates_commRing (X : Over (Spec (.of R))) [IsAffine X.left] :
    CommRing (T ⊗[R] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R X) :=
  Algebra.TensorProduct.instCommRing (R := R) (A := T) (B := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R X)

def affineBaseChangeCoordinates (X : Over (Spec (.of R))) [IsAffine X.left] :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R T)))).obj X ≅
      EtaleSplittingAt.EtaleSplitting.affineOver T (T ⊗[R] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R X) := by
  let A := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R X
  let a : X ≅ EtaleSplittingAt.EtaleSplitting.affineOver R A := HilbertConstruction.Affine.OverChartPoints.affineOverIso R X
  exact (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R T)))).mapIso a ≪≫
    (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R A T).symm

theorem affineBaseChangeCoordinates_natural
    {X Y : Over (Spec (.of R))} [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) :
    (affineBaseChangeCoordinates R T X).hom ≫
        AlgebraAutomorphismNaturality.affineOverAlgHom T (T ⊗[R] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R Y)
          (T ⊗[R] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R X)
          (Algebra.TensorProduct.map (AlgHom.id T T) (HilbertConstruction.Affine.OverMorphisms.affineOverMap R f)) =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R T)))).map f ≫
        (affineBaseChangeCoordinates R T Y).hom := by
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R T)))
  let A := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R X
  let B := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R Y
  let ex : X ≅ EtaleSplittingAt.EtaleSplitting.affineOver R A := HilbertConstruction.Affine.OverChartPoints.affineOverIso R X
  let ey : Y ≅ EtaleSplittingAt.EtaleSplitting.affineOver R B := HilbertConstruction.Affine.OverChartPoints.affineOverIso R Y
  let q := HilbertConstruction.Affine.OverMorphisms.affineOverMap R f
  let M := AlgebraAutomorphismNaturality.affineOverAlgHom T (T ⊗[R] B) (T ⊗[R] A)
    (Algebra.TensorProduct.map (AlgHom.id T T) q)
  have hb : (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R A T).hom ≫ F.map (AlgebraAutomorphismNaturality.affineOverAlgHom R B A q) =
      M ≫ (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R B T).hom := AlgebraAutomorphismNaturality.affineBaseChangeIso_natural R B A T q
  have hi := IsoNaturalitySquares.iso_inverse_square (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R A T)
    (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R B T) M (F.map (AlgebraAutomorphismNaturality.affineOverAlgHom R B A q)) hb
  have hn : f ≫ ey.hom = ex.hom ≫ AlgebraAutomorphismNaturality.affineOverAlgHom R B A q := HilbertConstruction.Affine.CoordinateDiagramIso.affineOverIso_natural R f
  calc
    (affineBaseChangeCoordinates R T X).hom ≫ M =
        (F.map ex.hom ≫ (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R A T).inv) ≫ M := rfl
    _ = F.map ex.hom ≫ ((EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R A T).inv ≫ M) := Category.assoc _ _ _
    _ = F.map ex.hom ≫
        (F.map (AlgebraAutomorphismNaturality.affineOverAlgHom R B A q) ≫ (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R B T).inv) := by rw [hi]
    _ = F.map (ex.hom ≫ AlgebraAutomorphismNaturality.affineOverAlgHom R B A q) ≫ (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R B T).inv := by
      rw [F.map_comp, Category.assoc]
    _ = F.map (f ≫ ey.hom) ≫ (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R B T).inv := by rw [← hn]
    _ = F.map f ≫ (affineBaseChangeCoordinates R T Y).hom := by
      rw [F.map_comp, Category.assoc]
      rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.BaseChangeCoordinates
