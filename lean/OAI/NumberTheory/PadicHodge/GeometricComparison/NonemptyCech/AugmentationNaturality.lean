import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Augmentation

/-! # Augmentation Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.AugmentationNaturality.NonemptyCechAugmentationNaturality

noncomputable section

/-! The canonical Čech augmentation is natural in its coefficient cone
and its source, at the original cochain-map level. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v w z t
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Preadditive A] [HasProducts.{t} A] [HasZeroObject A]
  {ι : Type t} (U : ι → C) {P Q : Cᵒᵖ ⥤ A} {M N : A}
  (η : (Functor.const Cᵒᵖ).obj M ⟶ P)

theorem coefficients (α : P ⟶ Q) :
    Augmentation.NonemptyCechAugmentation.augmentation U P M η ≫ (IntegralComparison.NonemptyCechNerve.complexFunctor U).map α =
      Augmentation.NonemptyCechAugmentation.augmentation U Q M (η ≫ α) := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, Augmentation.NonemptyCechAugmentation.augmentation_zero,
    Augmentation.NonemptyCechAugmentation.augmentation_zero]
  change Pi.lift (fun i : Fin 1 → ι => η.app (op (∏ᶜ (U ∘ i)))) ≫
      Limits.Pi.map (fun i : Fin 1 → ι => α.app (op (∏ᶜ (U ∘ i)))) =
    Pi.lift (fun i : Fin 1 → ι => η.app (op (∏ᶜ (U ∘ i))) ≫ α.app (op (∏ᶜ (U ∘ i))))
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, Pi.map_π, Pi.lift_comp_π, Pi.lift_comp_π_assoc]

theorem source (β : N ⟶ M) :
    (CochainComplex.single₀ A).map β ≫ Augmentation.NonemptyCechAugmentation.augmentation U P M η =
      Augmentation.NonemptyCechAugmentation.augmentation U P N ((Functor.const Cᵒᵖ).map β ≫ η) := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
    Augmentation.NonemptyCechAugmentation.augmentation_zero, Augmentation.NonemptyCechAugmentation.augmentation_zero]
  change β ≫ Pi.lift (fun i : Fin 1 → ι => η.app (op (∏ᶜ (U ∘ i)))) =
    Pi.lift (fun i : Fin 1 → ι => β ≫ η.app (op (∏ᶜ (U ∘ i))))
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, Pi.lift_comp_π]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.AugmentationNaturality.NonemptyCechAugmentationNaturality
