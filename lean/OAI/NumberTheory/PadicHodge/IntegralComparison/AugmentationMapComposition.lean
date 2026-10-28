import Mathlib.CategoryTheory.Iso

/-! # Augmentation Map Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentationMapComposition

/-! Composing augmentation-preserving maps with a source identification. -/

open _root_.CategoryTheory

theorem transport {C : Type*} [Category* C] {Z Z' K₀ K₁ K₂ K₃ : C}
    (e : Z' ≅ Z) (f₁ : K₀ ⟶ K₁) (f₂ : K₁ ⟶ K₂) (f₃ : K₂ ⟶ K₃)
    (a : Z' ⟶ K₀) (b : Z' ⟶ K₁) (c : Z' ⟶ K₂) (d : Z ⟶ K₃)
    (h₁ : a ≫ f₁ = b) (h₂ : b ≫ f₂ = c) (h₃ : c ≫ f₃ = e.hom ≫ d) :
    (e.inv ≫ a) ≫ (f₁ ≫ f₂ ≫ f₃) = d := by
  calc
    (e.inv ≫ a) ≫ (f₁ ≫ f₂ ≫ f₃) = e.inv ≫ ((a ≫ f₁) ≫ f₂) ≫ f₃ := by simp only [Category.assoc]
    _ = e.inv ≫ c ≫ f₃ := by rw [h₁, h₂]
    _ = e.inv ≫ e.hom ≫ d := by rw [h₃]
    _ = d := e.inv_hom_id_assoc d

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentationMapComposition
