import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.CohomologyLifts

/-! # Transition Cocycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf

noncomputable section

/-! Transition cocycles obtained from actual local lifts in a short exact sequence. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

def TransitionCocycle.sheafSectionRestrict (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {U V : Opens X} (h : V ≤ U) : F.obj.obj (op U) →+ F.obj.obj (op V) :=
  (F.obj.map (homOfLE h).op).hom

theorem TransitionCocycle.sheafSectionRestrict_comp (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V) (s : F.obj.obj (op U)) :
    TransitionCocycle.sheafSectionRestrict F hWV (TransitionCocycle.sheafSectionRestrict F hVU s) =
      TransitionCocycle.sheafSectionRestrict F (hWV.trans hVU) s := by
  change (F.obj.map (homOfLE hWV).op) ((F.obj.map (homOfLE hVU).op) s) = _
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
  rfl

theorem TransitionCocycle.sheafSectionMap_restrict {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (φ : F ⟶ G) {U V : Opens X} (h : V ≤ U) (s : F.obj.obj (op U)) :
    φ.hom.app (op V) (TransitionCocycle.sheafSectionRestrict F h s) =
      TransitionCocycle.sheafSectionRestrict G h (φ.hom.app (op U) s) :=
  ConcreteCategory.congr_hom (φ.hom.naturality (homOfLE h).op) s

theorem TransitionCocycle.sheafMono_section_injective {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (φ : F ⟶ G) [Mono φ] (U : Opens X) : Function.Injective (φ.hom.app (op U)) := by
  have hφ : Mono φ.hom := (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mp inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app φ.hom).mp hφ (op U))

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)} (hS : S.ShortExact)
variable {t : S.X₃.obj.obj (op (⊤ : Opens X))} (l : CohomologyLifts.SheafLocalLiftCover S.g t)

def CohomologyLifts.SheafLocalLiftCover.difference (i j : X) : S.X₂.obj.obj (op (l.domain i ⊓ l.domain j)) :=
  TransitionCocycle.sheafSectionRestrict S.X₂ inf_le_right (l.section_ j) -
    TransitionCocycle.sheafSectionRestrict S.X₂ inf_le_left (l.section_ i)

theorem CohomologyLifts.SheafLocalLiftCover.difference_image (i j : X) :
    S.g.hom.app (op (l.domain i ⊓ l.domain j)) (l.difference i j) = 0 := by
  simp only [CohomologyLifts.SheafLocalLiftCover.difference, map_sub, TransitionCocycle.sheafSectionMap_restrict, l.image]
  change TransitionCocycle.sheafSectionRestrict S.X₃ inf_le_right (TransitionCocycle.sheafSectionRestrict S.X₃ le_top t) -
    TransitionCocycle.sheafSectionRestrict S.X₃ inf_le_left (TransitionCocycle.sheafSectionRestrict S.X₃ le_top t) = 0
  rw [TransitionCocycle.sheafSectionRestrict_comp, TransitionCocycle.sheafSectionRestrict_comp, sub_self]

include hS in
theorem CohomologyLifts.SheafLocalLiftCover.exists_transition (i j : X) :
    ∃ s : S.X₁.obj.obj (op (l.domain i ⊓ l.domain j)),
      S.f.hom.app (op (l.domain i ⊓ l.domain j)) s = l.difference i j :=
  TopCat.Sheaf.sections_exact_of_left_exact hS.exact hS.mono_f _ (l.difference_image i j)

def CohomologyLifts.SheafLocalLiftCover.transition (i j : X) : S.X₁.obj.obj (op (l.domain i ⊓ l.domain j)) :=
  Classical.choose (l.exists_transition hS i j)

theorem CohomologyLifts.SheafLocalLiftCover.transition_map (i j : X) :
    S.f.hom.app (op (l.domain i ⊓ l.domain j)) (l.transition hS i j) = l.difference i j :=
  Classical.choose_spec (l.exists_transition hS i j)

/-- Restrictions of the chosen transitions satisfy the actual triple-overlap equation. -/
theorem CohomologyLifts.SheafLocalLiftCover.transition_cocycle (i j k : X) :
    TransitionCocycle.sheafSectionRestrict S.X₁ inf_le_left (l.transition hS i j) +
      TransitionCocycle.sheafSectionRestrict S.X₁ (inf_le_inf inf_le_right le_rfl) (l.transition hS j k) =
      TransitionCocycle.sheafSectionRestrict S.X₁ (inf_le_inf inf_le_left le_rfl) (l.transition hS i k) := by
  have : Mono S.f := hS.mono_f
  apply TransitionCocycle.sheafMono_section_injective S.f (l.domain i ⊓ l.domain j ⊓ l.domain k)
  simp only [map_add, TransitionCocycle.sheafSectionMap_restrict, CohomologyLifts.SheafLocalLiftCover.transition_map, CohomologyLifts.SheafLocalLiftCover.difference, map_sub,
    TransitionCocycle.sheafSectionRestrict_comp]
  abel

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf
