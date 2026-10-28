import Mathlib.CategoryTheory.Category.Basic

/-! # Morphism Factorization Induction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MorphismFactorizationInduction

/-! Predicate transport along identity compositions and common
factorizations, before specialization to concrete families. -/

open _root_.CategoryTheory
universe u v

theorem morphismPredicate_of_comp_id
    {C : Type u} [Category.{v} C] {A B : C}
    (Q : (A ⟶ B) → Prop) (a : A ⟶ B) (h : Q (a ≫ 𝟙 B)) : Q a := by
  simpa only [Category.comp_id] using h

theorem tripleMorphismFactorization_induction
    {C : Type u} [Category.{v} C] {T W A B D : C}
    (a₀ : W ⟶ A) (b₀ : W ⟶ B) (c₀ : W ⟶ D)
    (Q : (T ⟶ A) → (T ⟶ B) → (T ⟶ D) → Prop)
    (hQ : ∀ t : T ⟶ W, Q (t ≫ a₀) (t ≫ b₀) (t ≫ c₀))
    (a : T ⟶ A) (b : T ⟶ B) (c : T ⟶ D)
    (h : ∃ t : T ⟶ W, t ≫ a₀ = a ∧ t ≫ b₀ = b ∧ t ≫ c₀ = c) : Q a b c := by
  obtain ⟨t, ha, hb, hc⟩ := h
  subst a
  subst b
  subst c
  exact hQ t

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MorphismFactorizationInduction
