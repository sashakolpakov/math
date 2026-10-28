import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.Single

/-! # Augmentation Zero -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.AugmentationZero.MappedAugmentationZero

noncomputable section

/-! # Degree zero of the actual transported augmentation -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive] {Z : C} {K : CochainComplex C ℕ}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K)

theorem mapped :
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).inv.app Z ≫
      (F.mapHomologicalComplex (.up ℕ)).map ι).f 0 = F.map (ι.f 0) := by
  rw [HomologicalComplex.comp_f, HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  change (𝟙 _ ≫ F.map (𝟙 Z)) ≫ F.map (ι.f 0) = F.map (ι.f 0)
  rw [F.map_id, Category.id_comp, Category.id_comp]
  rfl

theorem normalized {Z' : D} (e : F.obj Z ≅ Z') :
    ((CochainComplex.single₀ D).map e.inv ≫
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).inv.app Z ≫
        (F.mapHomologicalComplex (.up ℕ)).map ι).f 0 = e.inv ≫ F.map (ι.f 0) := by
  rw [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero, mapped]
  rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.AugmentationZero.MappedAugmentationZero
