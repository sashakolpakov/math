import OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodColimit

/-! # Neighborhood Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodRestriction

noncomputable section

/-!
# IntegralComparison: neighborhood-colimit inverse-image values restrict functorially along actual site maps
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Neighborhoods OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodColimit

universe u v w u' v'

variable {C : Type u} [Category.{v} C] {A : Type w} [SemilatticeInf A]
  {D : Type u'} [Category.{v'} D] (P : A → ObjectProperty C)
  (hIncoming : ∀ V {T U : C}, (T ⟶ U) → P V U → P V T)
  [∀ T, HasColimitsOfShape (Incoming.Neighborhoods.Objects P T)ᵒᵖ D]
  {T U : C} (α : T ⟶ U) (F : Aᵒᵖ ⥤ D)

def restriction : colimit (NeighborhoodColimit.diagram P U F) ⟶ colimit (NeighborhoodColimit.diagram P T F) :=
  colimit.pre (NeighborhoodColimit.diagram P T F) (Incoming.Neighborhoods.change P hIncoming α).op

theorem ι_restriction (V : (Incoming.Neighborhoods.Objects P U)ᵒᵖ) : colimit.ι (NeighborhoodColimit.diagram P U F) V ≫ restriction P hIncoming α F =
    colimit.ι (NeighborhoodColimit.diagram P T F) ((Incoming.Neighborhoods.change P hIncoming α).op.obj V) :=
  colimit.ι_pre (NeighborhoodColimit.diagram P T F) (Incoming.Neighborhoods.change P hIncoming α).op V

omit α in
theorem restriction_id (T : C) : restriction P hIncoming (𝟙 T) F = 𝟙 (colimit (NeighborhoodColimit.diagram P T F)) := by
  apply colimit.hom_ext
  intro V
  exact (ι_restriction P hIncoming (𝟙 T) F V).trans (Category.comp_id _).symm

theorem restriction_comp {S : C} (β : U ⟶ S) : restriction P hIncoming (α ≫ β) F =
    restriction P hIncoming β F ≫ restriction P hIncoming α F := by
  apply colimit.hom_ext
  intro V
  exact (ι_restriction P hIncoming (α ≫ β) F V).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ restriction P hIncoming α F) (ι_restriction P hIncoming β F V)).trans
        (ι_restriction P hIncoming α F ((Incoming.Neighborhoods.change P hIncoming β).op.obj V)))).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodRestriction
