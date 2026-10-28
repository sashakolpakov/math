import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-! # Ext Extensions -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtExtensions.Construction

noncomputable section

/-!
# Completion: concrete short exact extensions representing degree-one classes

These constructions preserve the actual Ext group used by sheaf H¹.
A class is represented by pulling back an injective presentation, and its
vanishing is equivalent to a section of the resulting epimorphism.
-/

open _root_.CategoryTheory Limits Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Pull back the last map of a short complex, retaining its first object. -/
def pullbackExtensionComplex (S : ShortComplex C) {Z : C} (a : Z ⟶ S.X₃) : ShortComplex C :=
  ShortComplex.mk (pullback.lift S.f 0 (by simp [S.zero])) (pullback.snd S.g a)
    (by simp)

theorem pullbackExtensionComplex_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    {Z : C} (a : Z ⟶ S.X₃) : (pullbackExtensionComplex S a).ShortExact := by
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  let T := pullbackExtensionComplex S a
  have hm : Mono T.f := mono_of_mono_fac (pullback.lift_fst S.f 0 (by simp [S.zero]))
  have he : Epi T.g := inferInstanceAs (Epi (pullback.snd S.g a))
  refine ShortComplex.ShortExact.mk' ?_ hm he
  apply ShortComplex.exact_of_f_is_kernel
  apply KernelFork.IsLimit.ofι'
  intro W k hk
  have hk' : (k ≫ pullback.fst S.g a) ≫ S.g = 0 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (k ≫ T.g) ≫ a = 0
    rw [hk, zero_comp]
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hS.exact.fIsKernel _ hk'
  refine ⟨l, ?_⟩
  apply pullback.hom_ext
  · simpa [T, pullbackExtensionComplex, Category.assoc] using hl
  · simpa [T, pullbackExtensionComplex, Category.assoc] using hk.symm

/-- The canonical morphism from a pulled-back extension to the original one. -/
def pullbackExtensionMorphism (S : ShortComplex C) {Z : C} (a : Z ⟶ S.X₃) :
    pullbackExtensionComplex S a ⟶ S where
  τ₁ := 𝟙 _
  τ₂ := pullback.fst S.g a
  τ₃ := a
  comm₁₂ := by simp [pullbackExtensionComplex]
  comm₂₃ := pullback.condition

variable [HasExt.{w} C]

theorem pullbackExtensionComplex_extClass {S : ShortComplex C} (hS : S.ShortExact)
    {Z : C} (a : Z ⟶ S.X₃) :
    (pullbackExtensionComplex_shortExact hS a).extClass =
      (Ext.mk₀ a).comp hS.extClass (zero_add 1) := by
  have h := ShortComplex.ShortExact.extClass_naturality
    (pullbackExtensionComplex_shortExact hS a) hS (pullbackExtensionMorphism S a)
  simpa [pullbackExtensionMorphism] using h

/-- Every actual Ext¹ class has a short exact extension representative. -/
theorem ext_one_exists_shortExact [EnoughInjectives C] {X Y : C} (x : Ext X Y 1) :
    ∃ (E : C) (i : Y ⟶ E) (p : E ⟶ X) (h : i ≫ p = 0)
      (hs : (ShortComplex.mk i p h).ShortExact), hs.extClass = x := by
  let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι Y))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ X hS x (Ext.eq_zero_of_injective _) rfl
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective X S.X₃).surjective y
  let T := pullbackExtensionComplex S a
  exact ⟨T.X₂, T.f, T.g, T.zero, pullbackExtensionComplex_shortExact hS a,
    (pullbackExtensionComplex_extClass hS a).trans hy⟩

/-- Vanishing of an extension class is exactly existence of a splitting. -/
theorem extClass_eq_zero_iff_exists_section {S : ShortComplex C} (hS : S.ShortExact) :
    hS.extClass = 0 ↔ ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 _ := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ S.X₃ hS (Ext.mk₀ (𝟙 S.X₃)) rfl
      (by simp [hx])
    obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective S.X₃ S.X₂).surjective y
    refine ⟨s, (Ext.mk₀_bijective S.X₃ S.X₃).injective ?_⟩
    simpa only [Ext.mk₀_comp_mk₀] using hy
  · rintro ⟨s, hs⟩
    have h := congrArg (fun z : Ext S.X₂ S.X₁ 1 => (Ext.mk₀ s).comp z (zero_add 1))
      hS.comp_extClass
    simpa only [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      hs, Ext.mk₀_id_comp, Ext.comp_zero] using h

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtExtensions.Construction
