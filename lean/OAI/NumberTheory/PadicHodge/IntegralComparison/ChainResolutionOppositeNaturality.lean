import OAI.NumberTheory.PadicHodge.IntegralComparison.ChainResolutionOpposite

/-! # Chain Resolution Opposite Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ChainResolutionOppositeNaturality

noncomputable section

/-! Original augmented chain maps give the corresponding augmented maps after taking opposites. -/

open _root_.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  (P Q : ChainComplex C ℕ) {Z W : C}
  (ε : P ⟶ (ChainComplex.single₀ C).obj Z) (η : Q ⟶ (ChainComplex.single₀ C).obj W)
  (β : Q ⟶ P) (g : W ⟶ Z) (hβ : β.f 0 ≫ ε.f 0 = η.f 0 ≫ g)

include hβ in
theorem augmentation : ChainResolutionOpposite.augmentation P ε ≫
    (HomologicalComplex.opFunctor C (.down ℕ)).map β.op =
      (CochainComplex.single₀ Cᵒᵖ).map g.op ≫ ChainResolutionOpposite.augmentation Q η := by
  apply HomologicalComplex.from_single_hom_ext
  change (ChainResolutionOpposite.augmentation P ε).f 0 ≫ (β.f 0).op =
    ((CochainComplex.single₀ Cᵒᵖ).map g.op).f 0 ≫ (ChainResolutionOpposite.augmentation Q η).f 0
  rw [ChainResolutionOpposite.augmentation_zero, ChainResolutionOpposite.augmentation_zero,
    CochainComplex.single₀_map_f_zero]
  exact congrArg Quiver.Hom.op hβ

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ChainResolutionOppositeNaturality
