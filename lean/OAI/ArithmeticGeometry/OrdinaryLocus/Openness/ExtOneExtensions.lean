import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ShortExactPullback

/-! # Ext One Extensions -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ExtOneExtensions.Construction

noncomputable section

/-! Realizing first Ext classes by short exact extensions with specified endpoints. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Abelian

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem pullbackShortComplex_extClass (S : ShortComplex C) {P : C}
    (q : P ⟶ S.X₃) (hS : S.ShortExact) :
    (ShortExactPullback.Construction.pullbackShortComplex_shortExact S q hS).extClass =
      (Ext.mk₀ q).comp hS.extClass (zero_add 1) := by
  have he := ShortComplex.ShortExact.extClass_naturality
    (ShortExactPullback.Construction.pullbackShortComplex_shortExact S q hS) hS (ShortExactPullback.Construction.pullbackShortComplexMap S q)
  change (ShortExactPullback.Construction.pullbackShortComplex_shortExact S q hS).extClass.comp (Ext.mk₀ (𝟙 S.X₁)) _ = _ at he
  rw [Ext.comp_mk₀_id] at he
  exact he

theorem ext_one_has_extension [EnoughInjectives C] (P F : C) (e : Ext P F 1) :
    ∃ (E : C) (a : F ⟶ E) (b : E ⟶ P) (hab : a ≫ b = 0)
      (hS : (ShortComplex.mk a b hab).ShortExact), hS.extClass = e := by
  let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
    (cokernel.condition (Injective.ι F))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  obtain ⟨q, hq⟩ := Ext.covariant_sequence_exact₁ P hS e
    (Ext.eq_zero_of_injective _) (rfl : 0 + 1 = 1)
  obtain ⟨q', rfl⟩ := (Ext.mk₀_bijective _ _).surjective q
  exact ⟨(ShortExactPullback.Construction.pullbackShortComplex S q').X₂, (ShortExactPullback.Construction.pullbackShortComplex S q').f,
    (ShortExactPullback.Construction.pullbackShortComplex S q').g, (ShortExactPullback.Construction.pullbackShortComplex S q').zero,
    ShortExactPullback.Construction.pullbackShortComplex_shortExact S q' hS, (pullbackShortComplex_extClass S q' hS).trans hq⟩

theorem extClass_comp_zero_iff_extends (S : ShortComplex C) (hS : S.ShortExact)
    {G : C} (φ : S.X₁ ⟶ G) :
    hS.extClass.comp (Ext.mk₀ φ) (add_zero 1) = 0 ↔ ∃ t : S.X₂ ⟶ G, S.f ≫ t = φ := by
  constructor
  · intro hφ
    obtain ⟨t, ht⟩ := Ext.contravariant_sequence_exact₁ hS G (Ext.mk₀ φ)
      (rfl : 1 + 0 = 1) hφ
    obtain ⟨t', rfl⟩ := (Ext.mk₀_bijective _ _).surjective t
    exact ⟨t', (Ext.mk₀_bijective _ _).injective ((Ext.mk₀_comp_mk₀ S.f t').symm.trans ht)⟩
  · rintro ⟨t, rfl⟩
    rw [← Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc (Ext.mk₀ t)

theorem extClass_eq_zero_of_section (S : ShortComplex C) (hS : S.ShortExact)
    (t : S.X₃ ⟶ S.X₂) (ht : t ≫ S.g = 𝟙 _) : hS.extClass = 0 := by
  calc
    hS.extClass = (Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (zero_add 1) :=
      (Ext.mk₀_id_comp _).symm
    _ = (Ext.mk₀ (t ≫ S.g)).comp hS.extClass (zero_add 1) := by rw [ht]
    _ = 0 := by rw [← Ext.mk₀_comp_mk₀_assoc, hS.comp_extClass, Ext.comp_zero]

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ExtOneExtensions.Construction
