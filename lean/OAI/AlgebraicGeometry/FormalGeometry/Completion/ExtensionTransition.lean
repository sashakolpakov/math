import OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtPushout

/-! # Extension Transition -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtensionTransition.Construction

noncomputable section

/-!
# Completion: compatible splittings after a coefficient transition

Pushouts of one extension form a compatible family under coefficient maps.
Surjectivity on coefficient-valued morphisms lifts a prescribed splitting
at one level to a compatible splitting at the next.
-/

open _root_.CategoryTheory Limits Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  (S : ShortComplex C) {A B : C}
  (a : S.X₁ ⟶ A) (b : S.X₁ ⟶ B) (r : A ⟶ B) (hr : a ≫ r = b)

/-- The map between two coefficient pushouts induced by a compatible transition. -/
def pushoutExtensionTransition :
    (ExtPushout.Construction.pushoutExtensionComplex S a).X₂ ⟶ (ExtPushout.Construction.pushoutExtensionComplex S b).X₂ :=
  pushout.desc (pushout.inl S.f b) (r ≫ pushout.inr S.f b) (by
    rw [← Category.assoc, hr, ← pushout.condition])

@[reassoc (attr := simp)]
theorem pushoutExtensionTransition_inl :
    pushout.inl S.f a ≫ pushoutExtensionTransition S a b r hr = pushout.inl S.f b :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem pushoutExtensionTransition_inr :
    pushout.inr S.f a ≫ pushoutExtensionTransition S a b r hr = r ≫ pushout.inr S.f b :=
  pushout.inr_desc _ _ _

@[reassoc (attr := simp)]
theorem pushoutExtensionTransition_g :
    pushoutExtensionTransition S a b r hr ≫ (ExtPushout.Construction.pushoutExtensionComplex S b).g =
      (ExtPushout.Construction.pushoutExtensionComplex S a).g := by
  apply pushout.hom_ext <;> simp [ExtPushout.Construction.pushoutExtensionComplex]

/-- Lift a chosen splitting compatibly along a coefficient transition. -/
theorem exists_compatible_pushout_section (hS : S.ShortExact)
    (hlift : Function.Surjective (fun d : S.X₃ ⟶ A => d ≫ r))
    (sA : S.X₃ ⟶ (ExtPushout.Construction.pushoutExtensionComplex S a).X₂)
    (hsA : sA ≫ (ExtPushout.Construction.pushoutExtensionComplex S a).g = 𝟙 _)
    (sB : S.X₃ ⟶ (ExtPushout.Construction.pushoutExtensionComplex S b).X₂)
    (hsB : sB ≫ (ExtPushout.Construction.pushoutExtensionComplex S b).g = 𝟙 _) :
    ∃ s : S.X₃ ⟶ (ExtPushout.Construction.pushoutExtensionComplex S a).X₂,
      s ≫ (ExtPushout.Construction.pushoutExtensionComplex S a).g = 𝟙 _ ∧
      s ≫ pushoutExtensionTransition S a b r hr = sB := by
  let T := ExtPushout.Construction.pushoutExtensionComplex S b
  have hT : T.ShortExact := ExtPushout.Construction.pushoutExtensionComplex_shortExact hS b
  have : Mono T.f := hT.mono_f
  let d := sB - sA ≫ pushoutExtensionTransition S a b r hr
  have hd : d ≫ T.g = 0 := by
    change (sB - sA ≫ pushoutExtensionTransition S a b r hr) ≫
      (ExtPushout.Construction.pushoutExtensionComplex S b).g = 0
    rw [Preadditive.sub_comp, Category.assoc, pushoutExtensionTransition_g, hsA, hsB, sub_self]
  obtain ⟨e, he⟩ := KernelFork.IsLimit.lift' hT.exact.fIsKernel d hd
  change e ≫ T.f = d at he
  obtain ⟨e', he'⟩ := hlift e
  change e' ≫ r = e at he'
  refine ⟨sA + e' ≫ (ExtPushout.Construction.pushoutExtensionComplex S a).f, ?_, ?_⟩
  · simp only [Preadditive.add_comp, Category.assoc,
      (ExtPushout.Construction.pushoutExtensionComplex S a).zero, comp_zero, hsA, add_zero]
  · simp only [Preadditive.add_comp, Category.assoc]
    change sA ≫ pushoutExtensionTransition S a b r hr +
      e' ≫ pushout.inr S.f a ≫ pushoutExtensionTransition S a b r hr = sB
    rw [pushoutExtensionTransition_inr, ← Category.assoc]
    erw [he']
    change sA ≫ pushoutExtensionTransition S a b r hr + e ≫ T.f = sB
    rw [he]
    dsimp [d]
    abel

variable [HasExt.{w} C]

/-- A retraction of the first map kills the extension class. -/
theorem extClass_eq_zero_of_retraction (hS : S.ShortExact)
    (r : S.X₂ ⟶ S.X₁) (hr : S.f ≫ r = 𝟙 _) : hS.extClass = 0 := by
  have h := congrArg (fun z : Ext S.X₃ S.X₂ 1 => z.comp (Ext.mk₀ r) (add_zero 1))
    hS.extClass_comp
  simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hr,
    Ext.comp_mk₀_id, Ext.zero_comp] using h

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtensionTransition.Construction
