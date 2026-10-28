import OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtExtensions

/-! # Ext Pushout -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtPushout.Construction

noncomputable section

/-!
# Completion: changing coefficients in an actual extension

The pushout of the first map represents the induced Ext¹ class under a
coefficient map. This connects finite reduction of H¹ with split finite
coefficient extensions.
-/

open _root_.CategoryTheory Limits Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Push out the first map of an extension along a coefficient map. -/
def pushoutExtensionComplex (S : ShortComplex C) {Z : C} (a : S.X₁ ⟶ Z) : ShortComplex C :=
  ShortComplex.mk (pushout.inr S.f a) (pushout.desc S.g 0 (by simp [S.zero]))
    (by simp)

theorem pushoutExtensionComplex_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    {Z : C} (a : S.X₁ ⟶ Z) : (pushoutExtensionComplex S a).ShortExact := by
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  let T := pushoutExtensionComplex S a
  have hm : Mono T.f := inferInstanceAs (Mono (pushout.inr S.f a))
  have he : Epi T.g := epi_of_epi_fac (pushout.inl_desc S.g 0 (by simp [S.zero]))
  refine ShortComplex.ShortExact.mk' ?_ hm he
  apply ShortComplex.exact_of_g_is_cokernel
  apply CokernelCofork.IsColimit.ofπ'
  intro W k hk
  have hk' : S.f ≫ (pushout.inl S.f a ≫ k) = 0 := by
    rw [← Category.assoc, pushout.condition, Category.assoc]
    change a ≫ (T.f ≫ k) = 0
    rw [hk, comp_zero]
  obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' hS.exact.gIsCokernel _ hk'
  refine ⟨l, ?_⟩
  apply pushout.hom_ext
  · simpa [T, pushoutExtensionComplex, ← Category.assoc] using hl
  · simpa [T, pushoutExtensionComplex, ← Category.assoc] using hk.symm

/-- The canonical morphism into a changed-coefficient extension. -/
def pushoutExtensionMorphism (S : ShortComplex C) {Z : C} (a : S.X₁ ⟶ Z) :
    S ⟶ pushoutExtensionComplex S a where
  τ₁ := a
  τ₂ := pushout.inl S.f a
  τ₃ := 𝟙 _
  comm₁₂ := pushout.condition.symm
  comm₂₃ := by simp [pushoutExtensionComplex]

variable [HasExt.{w} C]

/-- Pushout represents the actual induced Ext¹ class under the coefficient map. -/
theorem pushoutExtensionComplex_extClass {S : ShortComplex C} (hS : S.ShortExact)
    {Z : C} (a : S.X₁ ⟶ Z) :
    (pushoutExtensionComplex_shortExact hS a).extClass =
      hS.extClass.comp (Ext.mk₀ a) (add_zero 1) := by
  have h := ShortComplex.ShortExact.extClass_naturality
    hS (pushoutExtensionComplex_shortExact hS a) (pushoutExtensionMorphism S a)
  simpa [pushoutExtensionMorphism] using h.symm

/-- Vanishing after changing coefficients is equivalent to a section of the pushout. -/
theorem extClass_coefficientMap_eq_zero_iff {S : ShortComplex C} (hS : S.ShortExact)
    {Z : C} (a : S.X₁ ⟶ Z) :
    hS.extClass.comp (Ext.mk₀ a) (add_zero 1) = 0 ↔
      ∃ s : S.X₃ ⟶ (pushoutExtensionComplex S a).X₂,
        s ≫ (pushoutExtensionComplex S a).g = 𝟙 _ := by
  rw [← pushoutExtensionComplex_extClass hS a]
  exact ExtExtensions.Construction.extClass_eq_zero_iff_exists_section (pushoutExtensionComplex_shortExact hS a)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtPushout.Construction
