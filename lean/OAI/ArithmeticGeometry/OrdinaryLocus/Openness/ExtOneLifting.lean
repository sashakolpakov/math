import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! # Ext One Lifting -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ExtOneLifting.Construction

noncomputable section

/-! A lifting criterion for vanishing of first Ext groups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Abelian

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
    [EnoughInjectives C] [HasExt.{w} C] (P F : C)

theorem ext_one_eq_zero_of_hom_lifting
    (hlift : ∀ (S : ShortComplex C) (_hS : S.ShortExact) (_hF : S.X₁ = F)
      (q : P ⟶ S.X₃), ∃ t : P ⟶ S.X₂, t ≫ S.g = q)
    (e : Ext P F 1) : e = 0 := by
  let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
    (cokernel.condition (Injective.ι F))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  obtain ⟨q, hq⟩ := Ext.covariant_sequence_exact₁ P hS e
    (Ext.eq_zero_of_injective _) (rfl : 0 + 1 = 1)
  obtain ⟨q', rfl⟩ := (Ext.mk₀_bijective _ _).surjective q
  obtain ⟨t, ht⟩ := hlift S hS rfl q'
  rw [← hq, ← ht, ← Ext.mk₀_comp_mk₀_assoc, hS.comp_extClass, Ext.comp_zero]

omit [EnoughInjectives C] in
theorem hom_lifting_of_ext_one_subsingleton [Subsingleton (Ext P F 1)]
    (S : ShortComplex C) (hS : S.ShortExact) (hF : S.X₁ = F)
    (q : P ⟶ S.X₃) : ∃ t : P ⟶ S.X₂, t ≫ S.g = q := by
  subst F
  obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₃ P hS (Ext.mk₀ q)
    (rfl : 0 + 1 = 1) (Subsingleton.elim _ 0)
  obtain ⟨t', rfl⟩ := (Ext.mk₀_bijective _ _).surjective t
  refine ⟨t', (Ext.mk₀_bijective _ _).injective ?_⟩
  exact (Ext.mk₀_comp_mk₀ t' S.g).symm.trans ht

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ExtOneLifting.Construction
