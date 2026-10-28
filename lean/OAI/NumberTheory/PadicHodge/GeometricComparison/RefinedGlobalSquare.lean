import Mathlib.CategoryTheory.Category.Basic

/-! # Refined Global Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.RefinedGlobalSquare.RefinedComparisonGlobalSquare

/-! Refinement-compatible local comparison squares assemble with
the original global crystalline comparison in the common source. -/

open _root_.CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C]

theorem source {A B D P H : C} (a : A ⟶ B) (r : B ⟶ P) (e : B ⟶ H)
    (t : A ⟶ D) (c : D ⟶ P) (h : P ⟶ H)
    (hc : a ≫ r = t ≫ c) (hg : r ≫ h = e) : a ≫ e = t ≫ c ≫ h := by
  rw [← hg, ← Category.assoc, hc, Category.assoc]

theorem target {A B D₁ D₂ P₁ P₂ H₁ H₂ : C}
    (a : A ⟶ B) (r : B ⟶ P₂) (e : B ⟶ H₂) (g : H₂ ⟶ H₁)
    (t : A ⟶ D₂) (c₂ : D₂ ⟶ P₂) (b : P₂ ⟶ P₁)
    (d : D₂ ⟶ D₁) (c₁ : D₁ ⟶ P₁) (h : P₁ ⟶ H₁)
    (hc : a ≫ r = t ≫ c₂) (hb : c₂ ≫ b = d ≫ c₁)
    (hg : r ≫ b ≫ h = e ≫ g) : a ≫ e ≫ g = t ≫ d ≫ c₁ ≫ h := by
  rw [← hg, ← Category.assoc a r, hc, Category.assoc t c₂,
    ← Category.assoc c₂ b, hb, Category.assoc d c₁]

end OAI.NumberTheory.PadicHodge.GeometricComparison.RefinedGlobalSquare.RefinedComparisonGlobalSquare
