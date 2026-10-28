import Mathlib.CategoryTheory.Iso

/-! # Chart Augmentation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ChartAugmentation.ChartAugmentationAssembly

/-! Assembly of the original chart augmentation through the explicit
local frame and total comparison isomorphisms. -/

open _root_.CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C] {O A B E D T : C}
  (a : O ⟶ A) (b : O ⟶ B) (c : O ⟶ D) (u : B ⟶ E) (v : E ≅ A) (m : E ⟶ T) (e : D ≅ T)
  (ha : b ≫ (u ≫ v.hom) = a) (hc : c ≫ e.hom = b ≫ u ≫ m)

include ha hc in
theorem augmentation : a ≫ (v.inv ≫ m ≫ e.inv) = c := by
  apply (cancel_mono e.hom).mp
  rw [ha.symm]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
  exact hc.symm

end OAI.NumberTheory.PadicHodge.GeometricComparison.ChartAugmentation.ChartAugmentationAssembly
