import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Adjunction Augmentation Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AdjunctionAugmentationNormalization

/-! An augmentation transported through the left adjoint agrees with its
original map after the literal adjunction unit. -/

open _root_.CategoryTheory

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

theorem normalization {A P : C} {Y : D} (e : F.obj A ≅ Y)
    (j : A ⟶ G.obj Y) (hj : adj.unit.app A ≫ G.map e.hom = j)
    (a : A ⟶ P) (b : Y ⟶ F.obj P) (hb : b = e.inv ≫ F.map a) :
    j ≫ G.map b = a ≫ adj.unit.app P := by
  rw [← hj, hb, Functor.map_comp, Category.assoc, ← Category.assoc (G.map e.hom),
    ← Functor.map_comp, e.hom_inv_id, Functor.map_id, Category.id_comp]
  exact (adj.unit.naturality a).symm

end OAI.NumberTheory.PadicHodge.IntegralComparison.AdjunctionAugmentationNormalization
