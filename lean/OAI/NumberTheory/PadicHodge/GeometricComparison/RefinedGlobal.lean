import Mathlib.CategoryTheory.EpiMono

/-! # Refined Global -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.RefinedGlobal.RefinedGlobalConeNaturality

/-! Original global comparison maps are determined by their canonical
global edges. Compatibility of those edges proves naturality through
a common source refinement without a target-cover assumption. -/

open _root_.CategoryTheory

variable {C : Type*} [Category* C]
  {G₁ G₂ K₁ K₂ P₁ P₂ B₁ B₂ : C}
  (e₁ : G₁ ⟶ K₁) (e₂ : G₂ ⟶ K₂) [Epi e₁] [Epi e₂]
  (r₁ : K₁ ⟶ P₁) (r₂ : K₂ ⟶ P₂) (p₁ : G₁ ⟶ P₁) (p₂ : G₂ ⟶ P₂)
  (a : G₂ ⟶ G₁) (b : P₂ ⟶ P₁) (g : B₂ ⟶ B₁)
  (i₁ : K₁ ⟶ B₁) (i₂ : K₂ ⟶ B₂) (h : P₁ ⟶ B₁)
  (j₁ : G₁ ⟶ B₁) (j₂ : G₂ ⟶ B₂)
  (hr₁ : e₁ ≫ r₁ = p₁) (hr₂ : e₂ ≫ r₂ = p₂)
  (hb : p₂ ≫ b = a ≫ p₁) (hh : p₁ ≫ h = j₁)
  (ha : a ≫ j₁ = j₂ ≫ g) (hi₁ : e₁ ≫ i₁ = j₁) (hi₂ : e₂ ≫ i₂ = j₂)

include hr₁ hh hi₁ in
theorem source : r₁ ≫ h = i₁ := by
  apply (cancel_epi e₁).1
  rw [← Category.assoc, hr₁, hh, hi₁]

include hr₂ hb hh ha hi₂ in
theorem target : r₂ ≫ b ≫ h = i₂ ≫ g := by
  apply (cancel_epi e₂).1
  rw [← Category.assoc e₂ r₂, hr₂, ← Category.assoc p₂ b, hb,
    Category.assoc a p₁, hh, ha, ← Category.assoc e₂ i₂, hi₂]

end OAI.NumberTheory.PadicHodge.GeometricComparison.RefinedGlobal.RefinedGlobalConeNaturality
