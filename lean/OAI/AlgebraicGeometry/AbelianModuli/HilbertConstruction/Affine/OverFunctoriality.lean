import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverMorphisms

/-! # Over Functoriality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverFunctoriality

noncomputable section

/-! The coordinate-algebra maps preserve identities and reverse composition of affine scheme maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R]

theorem affineOverMap_id (X : Over (Spec (.of R))) [IsAffine X.left] :
    OverMorphisms.affineOverMap R (𝟙 X) = AlgHom.id R (OverChartPoints.affineOverAlgebra R X) := by
  simp [OverMorphisms.affineOverMap]

theorem affineOverMap_comp
    {X Y Z : Over (Spec (.of R))} [IsAffine X.left] [IsAffine Y.left] [IsAffine Z.left]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    OverMorphisms.affineOverMap R (f ≫ g) = (OverMorphisms.affineOverMap R f).comp (OverMorphisms.affineOverMap R g) := by
  have he : ((OverChartPoints.affineOverIso R X).inv ≫ f ≫ (OverChartPoints.affineOverIso R Y).hom) ≫
      ((OverChartPoints.affineOverIso R Y).inv ≫ g ≫ (OverChartPoints.affineOverIso R Z).hom) =
      (OverChartPoints.affineOverIso R X).inv ≫ (f ≫ g) ≫ (OverChartPoints.affineOverIso R Z).hom := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have h := (algSpec.fullyFaithful (R := CommRingCat.of R)).preimage_comp
    ((OverChartPoints.affineOverIso R X).inv ≫ f ≫ (OverChartPoints.affineOverIso R Y).hom)
    ((OverChartPoints.affineOverIso R Y).inv ≫ g ≫ (OverChartPoints.affineOverIso R Z).hom)
  rw [he] at h
  exact congrArg (fun k => k.unop.hom) h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverFunctoriality
