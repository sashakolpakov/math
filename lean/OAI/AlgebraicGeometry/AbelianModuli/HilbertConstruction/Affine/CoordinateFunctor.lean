import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverFunctoriality

/-! # Coordinate Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateFunctor

noncomputable section

/-! The coordinate rings of an affine scheme diagram form a contravariant algebra functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

def affineCoordinateFunctor (C : Type u) [CommRing C]
    {J : Type v} [Category.{w} J] (F : J ⥤ Over (Spec (.of C)))
    [∀ i, IsAffine (F.obj i).left] : Jᵒᵖ ⥤ CommAlgCat C where
  obj i := OverChartPoints.affineOverAlgebra C (F.obj i.unop)
  map {i j} h := CommAlgCat.ofHom
    (X := ↥(OverChartPoints.affineOverAlgebra C (F.obj i.unop)))
    (Y := ↥(OverChartPoints.affineOverAlgebra C (F.obj j.unop)))
    (OverMorphisms.affineOverMap C (F.map h.unop))
  map_id i := by
    apply CommAlgCat.hom_ext
    change OverMorphisms.affineOverMap C (F.map (𝟙 i.unop)) = AlgHom.id C (OverChartPoints.affineOverAlgebra C (F.obj i.unop))
    rw [F.map_id, OverFunctoriality.affineOverMap_id]
  map_comp f g := by
    apply CommAlgCat.hom_ext
    change OverMorphisms.affineOverMap C (F.map (g.unop ≫ f.unop)) =
      (OverMorphisms.affineOverMap C (F.map g.unop)).comp (OverMorphisms.affineOverMap C (F.map f.unop))
    rw [F.map_comp, OverFunctoriality.affineOverMap_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateFunctor
