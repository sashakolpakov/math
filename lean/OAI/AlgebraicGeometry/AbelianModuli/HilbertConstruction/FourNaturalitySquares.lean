import Mathlib.CategoryTheory.Category.Basic

/-! # Four Naturality Squares -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FourNaturalitySquares

open _root_.CategoryTheory

theorem fourNaturalitySquares {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : C}
    (f₁ : A₀ ⟶ A₁) (f₂ : A₁ ⟶ A₂) (f₃ : A₂ ⟶ A₃) (f₄ : A₃ ⟶ A₄)
    (g₁ : B₀ ⟶ B₁) (g₂ : B₁ ⟶ B₂) (g₃ : B₂ ⟶ B₃) (g₄ : B₃ ⟶ B₄)
    (z₀ : A₀ ⟶ B₀) (z₁ : A₁ ⟶ B₁) (z₂ : A₂ ⟶ B₂)
    (z₃ : A₃ ⟶ B₃) (z₄ : A₄ ⟶ B₄)
    (h₁ : z₀ ≫ g₁ = f₁ ≫ z₁) (h₂ : z₁ ≫ g₂ = f₂ ≫ z₂)
    (h₃ : z₂ ≫ g₃ = f₃ ≫ z₃) (h₄ : z₃ ≫ g₄ = f₄ ≫ z₄) :
    z₀ ≫ (g₁ ≫ (g₂ ≫ (g₃ ≫ g₄))) = (f₁ ≫ (f₂ ≫ (f₃ ≫ f₄))) ≫ z₄ := by
  rw [← Category.assoc z₀ g₁, h₁, Category.assoc,
    ← Category.assoc z₁ g₂, h₂, Category.assoc,
    ← Category.assoc z₂ g₃, h₃, Category.assoc, h₄]
  simp only [Category.assoc]

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FourNaturalitySquares
