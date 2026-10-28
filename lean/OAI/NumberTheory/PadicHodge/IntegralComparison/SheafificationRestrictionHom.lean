import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationSheafRestriction

/-! # Sheafification Restriction Hom -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SheafificationRestrictionHom

noncomputable section

/-! The original sheafification adjunction identifies restricted sheaf maps with their actual presheaf maps. -/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationSheafRestriction

universe u v w v' w'

variable (R : Type u) [CommRing R] {C : Type v} [Category.{w} C]
  {D : Type v'} [Category.{w'} D] (G : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J (ModuleCat.{u} R)] [HasSheafify K (ModuleCat.{u} R)]
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ (F : Cᵒᵖ ⥤ ModuleCat.{u} R), G.op.HasPointwiseRightKanExtension F]

theorem unit (B : Dᵒᵖ ⥤ ModuleCat.{u} R) :
    (sheafificationAdjunction J (ModuleCat.{u} R)).homEquiv _ _ ((Cech.PresentationSheafRestriction.compatibility R G J K).hom.app B) =
      (Cech.PresentationRestriction.restriction R G).map
        ((sheafificationAdjunction K (ModuleCat.{u} R)).unit.app B) := by
  rw [Adjunction.homEquiv_unit]
  exact G.toSheafify_pullbackSheafificationCompatibility (ModuleCat.{u} R) J K B

variable {A : Cᵒᵖ ⥤ ModuleCat.{u} R} {B : Dᵒᵖ ⥤ ModuleCat.{u} R}
  (a : A ⟶ G.op ⋙ B) {I : Sheaf K (ModuleCat.{u} R)}
  (f : (presheafToSheaf K (ModuleCat.{u} R)).obj B ⟶ I)

theorem hom : (sheafificationAdjunction J (ModuleCat.{u} R)).homEquiv A ((Cech.PresentationSheafRestriction.restriction R G J K).obj I)
    (((presheafToSheaf J (ModuleCat.{u} R)).map a ≫ (Cech.PresentationSheafRestriction.compatibility R G J K).hom.app B) ≫
      (Cech.PresentationSheafRestriction.restriction R G J K).map f) =
        a ≫ (Cech.PresentationRestriction.restriction R G).map
          ((sheafificationAdjunction K (ModuleCat.{u} R)).homEquiv B I f) := by
  let adj := sheafificationAdjunction J (ModuleCat.{u} R)
  let P := Cech.PresentationRestriction.restriction R G
  have hr := adj.homEquiv_naturality_right ((Cech.PresentationSheafRestriction.compatibility R G J K).hom.app B) ((Cech.PresentationSheafRestriction.restriction R G J K).map f)
  have hu := (congrArg (fun b => b ≫ ((Cech.PresentationSheafRestriction.restriction R G J K).map f).hom) (SheafificationRestrictionHom.unit R G J K B)).trans
    ((P.map_comp ((sheafificationAdjunction K (ModuleCat.{u} R)).unit.app B) f.hom).symm.trans
      (congrArg P.map (Adjunction.homEquiv_unit (sheafificationAdjunction K (ModuleCat.{u} R)) B I f).symm))
  exact (congrArg (adj.homEquiv A ((Cech.PresentationSheafRestriction.restriction R G J K).obj I)) (Category.assoc _ _ _)).trans
    ((adj.homEquiv_naturality_left a _).trans (congrArg (fun b => a ≫ b) (hr.trans hu)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SheafificationRestrictionHom
