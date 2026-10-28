import Mathlib.CategoryTheory.Iso

/-! # Augmentation Iso Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentationIsoComposition

/-!
# IntegralComparison: composing augmentation-preserving isomorphisms
-/

open _root_.CategoryTheory

universe u v

theorem transport {C : Type u} [Category.{v} C] {Z Z' K₀ K₁ K₂ K₃ : C}
    (e : Z' ≅ Z) (e₁ : K₀ ≅ K₁) (e₂ : K₁ ≅ K₂) (e₃ : K₂ ≅ K₃)
    (a : Z' ⟶ K₀) (b : Z' ⟶ K₁) (c : Z' ⟶ K₂) (d : Z ⟶ K₃)
    (h₁ : a ≫ e₁.hom = b) (h₂ : b ≫ e₂.hom = c) (h₃ : c ≫ e₃.hom = e.hom ≫ d) :
    (e.inv ≫ a) ≫ (e₁ ≪≫ e₂ ≪≫ e₃).hom = d := by
  calc
    (e.inv ≫ a) ≫ (e₁ ≪≫ e₂ ≪≫ e₃).hom = e.inv ≫ ((a ≫ e₁.hom) ≫ e₂.hom) ≫ e₃.hom := by
      simp only [Iso.trans_hom, Category.assoc]
    _ = e.inv ≫ c ≫ e₃.hom := by rw [h₁, h₂]
    _ = e.inv ≫ e.hom ≫ d := by rw [h₃]
    _ = d := e.inv_hom_id_assoc d

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentationIsoComposition
