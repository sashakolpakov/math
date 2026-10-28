import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Sheafification Transport Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SheafificationTransportUnit

noncomputable section

/-!
# IntegralComparison: transport of sheafification retains the original presheaf sections
-/

open _root_.CategoryTheory

universe u v u' v' w z

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (G : C ⥤ D) (A : Type w) [Category.{z} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension P]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  (P : Dᵒᵖ ⥤ A)

def comparison : sheafify J (G.op ⋙ P) ≅ G.op ⋙ sheafify K P :=
  (sheafToPresheaf J A).mapIso ((G.pushforwardContinuousSheafificationCompatibility A J K).app P)

theorem comparison_unit : toSheafify J (G.op ⋙ P) ≫ (comparison G A J K P).hom =
    Functor.whiskerLeft G.op (toSheafify K P) :=
  G.toSheafify_pullbackSheafificationCompatibility A J K P

theorem inverse_unit : Functor.whiskerLeft G.op (toSheafify K P) ≫ (comparison G A J K P).inv =
    toSheafify J (G.op ⋙ P) := by
  apply (cancel_mono (comparison G A J K P).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (comparison_unit G A J K P).symm

variable (Q : Cᵒᵖ ⥤ A) (e : G.op ⋙ P ≅ Q)

def transport : (G.sheafPushforwardContinuous A J K).obj ((presheafToSheaf K A).obj P) ≅
    (presheafToSheaf J A).obj Q :=
  (G.pushforwardContinuousSheafificationCompatibility A J K).symm.app P ≪≫
    (presheafToSheaf J A).mapIso e

theorem unit : Functor.whiskerLeft G.op (toSheafify K P) ≫ (transport G A J K P Q e).hom.hom =
    e.hom ≫ toSheafify J Q := by
  change Functor.whiskerLeft G.op (toSheafify K P) ≫
      ((comparison G A J K P).inv ≫ sheafifyMap J e.hom) = e.hom ≫ toSheafify J Q
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ sheafifyMap J e.hom) (inverse_unit G A J K P)).trans
      (CategoryTheory.toSheafify_naturality J e.hom).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SheafificationTransportUnit
