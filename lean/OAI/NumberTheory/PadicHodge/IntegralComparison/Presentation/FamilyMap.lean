import OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationPresheaf

/-! # Family Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.FamilyMap.Family

noncomputable section

/-! Maps of frame families induce the actual maps of their presentation presheaves. -/

open _root_.CategoryTheory Opposite

universe u v

variable {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
  (G : C ⥤ D) {ι : Type v} (F : ι → C) (H : ι → D) (a : ∀ i, G.obj (F i) ⟶ H i)

def map : CoveringPresentationPresheaf.presentations F ⟶
    G.op ⋙ CoveringPresentationPresheaf.presentations H where
  app _ := ↾fun x => ⟨⟨x.down.1, G.map x.down.2 ≫ a x.down.1⟩⟩
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    exact (congrArg (fun b => b ≫ a x.down.1) (G.map_comp f.unop x.down.2)).trans (Category.assoc _ _ _)

theorem bijective (h : ∀ (U : C) (i : ι), Function.Bijective (fun b : U ⟶ F i => G.map b ≫ a i)) (U : Cᵒᵖ) :
    Function.Bijective ((Family.map G F H a).app U) := by
  constructor
  · intro x y he
    have hi : x.down.1 = y.down.1 := congrArg (fun z => z.down.1) he
    rcases x with ⟨⟨i, b⟩⟩
    rcases y with ⟨⟨j, c⟩⟩
    dsimp only at hi
    subst j
    have hb : G.map b ≫ a i = G.map c ≫ a i :=
      eq_of_heq (Sigma.mk.inj_iff.mp (congrArg ULift.down he)).2
    exact congrArg (fun b => ULift.up (Sigma.mk i b)) ((h U.unop i).1 hb)
  · rintro ⟨⟨i, b⟩⟩
    obtain ⟨c, hc⟩ := (h U.unop i).2 b
    exact ⟨⟨⟨i, c⟩⟩, congrArg (fun b => ULift.up (Sigma.mk i b)) hc⟩

theorem isIso (h : ∀ (U : C) (i : ι), Function.Bijective (fun b : U ⟶ F i => G.map b ≫ a i)) :
    IsIso (Family.map G F H a) := by
  let (U : Cᵒᵖ) : IsIso ((Family.map G F H a).app U) :=
    (CategoryTheory.isIso_iff_bijective _).mpr (bijective G F H a h U)
  exact NatIso.isIso_of_isIso_app _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.FamilyMap.Family
