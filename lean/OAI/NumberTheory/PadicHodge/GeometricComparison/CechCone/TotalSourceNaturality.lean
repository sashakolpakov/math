import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.AugmentationNaturality

/-! # Total Source Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalSourceNaturality.CechConeTotalSourceNaturality

noncomputable section

/-! The original canonical total augmentation is natural in its
source complex, with its actual edge components retained. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z t
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{t} A] [HasCoproducts.{0} A]
  {ι : Type t} (U : ι → C) (P : Cᵒᵖ ⥤ CochainComplex A ℕ)
  (M N : CochainComplex A ℕ) (η : (Functor.const Cᵒᵖ).obj M ⟶ P) (β : N ⟶ M)

omit [HasCoproducts.{0} A] in
theorem zeroMap : β ≫ Total.CechConeTotal.zeroMap U P M η =
    Total.CechConeTotal.zeroMap U P N ((Functor.const Cᵒᵖ).map β ≫ η) := by
  have h := congrArg (fun α => α.f 0) (NonemptyCech.AugmentationNaturality.NonemptyCechAugmentationNaturality.source U η β)
  rw [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
    NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation_zero, NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation_zero] at h
  exact h

theorem augmentation : β ≫ Total.CechConeTotal.augmentation U P M η =
    Total.CechConeTotal.augmentation U P N ((Functor.const Cᵒᵖ).map β ≫ η) := by
  ext q : 1
  have hq := congrArg (fun α => α.f q) (zeroMap U P M N η β)
  change β.f q ≫ Total.CechConeTotal.component U P M η q =
    Total.CechConeTotal.component U P N ((Functor.const Cᵒᵖ).map β ≫ η) q at hq
  change β.f q ≫ (Total.CechConeTotal.component U P M η q ≫
      (Total.CechConeTotal.bicomplex U P).ιTotal (.up ℕ) q 0 q rfl) =
    Total.CechConeTotal.component U P N ((Functor.const Cᵒᵖ).map β ≫ η) q ≫
      (Total.CechConeTotal.bicomplex U P).ιTotal (.up ℕ) q 0 q rfl
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun α => α ≫ (Total.CechConeTotal.bicomplex U P).ιTotal (.up ℕ) q 0 q rfl) hq)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalSourceNaturality.CechConeTotalSourceNaturality
