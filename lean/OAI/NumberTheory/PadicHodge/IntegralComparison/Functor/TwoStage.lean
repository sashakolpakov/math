import Mathlib.CategoryTheory.Functor.Basic

/-! # Two Stage -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.TwoStage.Comparison

/-! Comparison maps remain compatible through two successive resolution transports. -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
  {A B K₀ K₁ K₂ K₃ : C} (a : A ⟶ K₀) (r : K₀ ⟶ K₁) (b : A ⟶ B)
  (c₁ : B ⟶ K₁) (c₂ : B ⟶ K₂) (c₃ : B ⟶ K₃) (q₁ : K₁ ⟶ K₂) (q₂ : K₂ ⟶ K₃)

theorem transport (h₀ : F.map (a ≫ r) = F.map (b ≫ c₁))
    (h₁ : F.map (c₁ ≫ q₁) = F.map c₂) (h₂ : F.map (c₂ ≫ q₂) = F.map c₃) :
    F.map (a ≫ r ≫ q₁ ≫ q₂) = F.map (b ≫ c₃) := by
  have h₀' : F.map a ≫ F.map r = F.map b ≫ F.map c₁ := by
    simpa only [F.map_comp] using h₀
  have h₁' : F.map c₁ ≫ F.map q₁ = F.map c₂ := by
    simpa only [F.map_comp] using h₁
  have h₂' : F.map c₂ ≫ F.map q₂ = F.map c₃ := by
    simpa only [F.map_comp] using h₂
  calc
    _ = (F.map a ≫ F.map r) ≫ F.map q₁ ≫ F.map q₂ := by simp only [F.map_comp, Category.assoc]
    _ = (F.map b ≫ F.map c₁) ≫ F.map q₁ ≫ F.map q₂ := by rw [h₀']
    _ = F.map b ≫ (F.map c₁ ≫ F.map q₁) ≫ F.map q₂ := by simp only [Category.assoc]
    _ = F.map b ≫ F.map c₂ ≫ F.map q₂ := by rw [h₁']
    _ = F.map b ≫ F.map c₃ := by rw [h₂']
    _ = F.map (b ≫ c₃) := (F.map_comp _ _).symm

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.TwoStage.Comparison
