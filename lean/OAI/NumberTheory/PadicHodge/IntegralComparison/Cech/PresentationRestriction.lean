import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationMap

/-! # Presentation Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationRestriction

noncomputable section

/-! The original free presentation chain complex commutes with restriction of presheaves. -/

open _root_.CategoryTheory

universe u v w v' w'

variable (R : Type u) [CommRing R] {C : Type v} [Category.{w} C]
  {D : Type v'} [Category.{w'} D] (G : C ⥤ D)

def restriction : (Dᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Cᵒᵖ ⥤ ModuleCat.{u} R) :=
  (Functor.whiskeringLeft _ _ _).obj G.op

instance restriction_additive : (restriction R G).Additive where
  map_add := by intros; rfl

def iso (H : Dᵒᵖ ⥤ Type u) : AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R (G.op ⋙ H) ≅
    ((restriction R G).mapHomologicalComplex (.down ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R H) :=
  Iso.refl _

theorem augmentation_zero (H : Dᵒᵖ ⥤ Type u) :
    (restriction R G).map ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R H).f 0) =
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R (G.op ⋙ H)).f 0 := rfl

variable {F : Cᵒᵖ ⥤ Type u} {H : Dᵒᵖ ⥤ Type u} (a : F ⟶ G.op ⋙ H)

def map : AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R F ⟶
    ((restriction R G).mapHomologicalComplex (.down ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R H) :=
  PresentationMap.map R a ≫ (iso R G H).hom

theorem map_augmentation_zero : (PresentationRestriction.map R G a).f 0 ≫
    (restriction R G).map ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R H).f 0) =
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R F).f 0 := by
  have h := congrArg (fun b => b.f 0) (PresentationMap.augmentation R a)
  change ((PresentationMap.map R a).f 0 ≫ 𝟙 _) ≫
    (restriction R G).map ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R H).f 0) = _
  exact (congrArg (fun b => b ≫ (restriction R G).map ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R H).f 0))
    (Category.comp_id ((PresentationMap.map R a).f 0))).trans h

instance map_isIso [IsIso a] : IsIso (PresentationRestriction.map R G a) := by
  dsimp only [PresentationRestriction.map]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationRestriction
