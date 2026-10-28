import Mathlib.CategoryTheory.Category.Basic

/-! # Coefficient Comparison Diagrams -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientComparisonDiagrams

/-! Compose the actual coefficient comparison squares without unfolding
their geometric objects. -/

open _root_.CategoryTheory

theorem two_comparison_squares {C : Type*} [Category C]
    {A₀ A₁ A₂ B₀ B₁ B₂ : C}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (a' : B₀ ⟶ B₁) (b' : B₁ ⟶ B₂)
    (u₀ : A₀ ⟶ B₀) (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂)
    (ha : a ≫ u₁ = u₀ ≫ a') (hb : b ≫ u₂ = u₁ ≫ b') :
    (a ≫ b) ≫ u₂ = u₀ ≫ a' ≫ b' := by
  rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc]

theorem three_comparison_squares {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : C}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃)
    (a' : B₀ ⟶ B₁) (b' : B₁ ⟶ B₂) (c' : B₂ ⟶ B₃)
    (u₀ : A₀ ⟶ B₀) (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂) (u₃ : A₃ ⟶ B₃)
    (ha : a ≫ u₁ = u₀ ≫ a') (hb : b ≫ u₂ = u₁ ≫ b') (hc : c ≫ u₃ = u₂ ≫ c') :
    (a ≫ b ≫ c) ≫ u₃ = u₀ ≫ a' ≫ b' ≫ c' := by
  rw [Category.assoc, Category.assoc, hc, ← Category.assoc b, hb,
    Category.assoc u₁, ← Category.assoc a, ha, Category.assoc]

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientComparisonDiagrams
