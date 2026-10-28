import OAI.AlgebraicGeometry.Comparison.Betti.AugmentationExtension

/-! # Augmentation Coefficient Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AugmentationCoefficientNormalization.ComplexExtension

noncomputable section

/-! Extension of the original augmentation preserves a coefficient map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {Y Z : C} {K : CochainComplex C ℕ}

theorem fromSingleAugmentation_precomp (u : Y ⟶ Z) (f : Z ⟶ K.X 0)
    (hf : f ≫ K.d 0 1 = 0) :
    (CochainComplex.fromSingle₀Equiv K Y).symm ⟨u ≫ f, by rw [Category.assoc, hf, comp_zero]⟩ =
      (CochainComplex.single₀ C).map u ≫ (CochainComplex.fromSingle₀Equiv K Z).symm ⟨f, hf⟩ := by
  apply HomologicalComplex.from_single_hom_ext
  erw [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
    CochainComplex.fromSingle₀Equiv_symm_apply_f_zero,
    CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  rfl

theorem augmentationZero_precomp (u : Y ⟶ Z) (a : (CochainComplex.single₀ C).obj Z ⟶ K) :
    AugmentationExtension.Complex.augmentationZero ((CochainComplex.single₀ C).map u ≫ a) = u ≫ AugmentationExtension.Complex.augmentationZero a := by
  unfold AugmentationExtension.Complex.augmentationZero
  simp only [HomologicalComplex.comp_f, CochainComplex.single₀ObjXSelf, Iso.refl_inv]
  erw [CochainComplex.single₀_map_f_zero, Category.id_comp, Category.id_comp]
  rfl

theorem extendAugmentation_precomp (u : Y ⟶ Z) (a : (CochainComplex.single₀ C).obj Z ⟶ K) :
    AugmentationExtension.Complex.extendAugmentation ((CochainComplex.single₀ C).map u ≫ a) =
      (CochainComplex.singleFunctor C 0).map u ≫ AugmentationExtension.Complex.extendAugmentation a := by
  apply HomologicalComplex.from_single_hom_ext
  change (AugmentationExtension.Complex.extendAugmentation ((CochainComplex.single₀ C).map u ≫ a)).f 0 =
    ((CochainComplex.singleFunctor C 0).map u).f 0 ≫ (AugmentationExtension.Complex.extendAugmentation a).f 0
  erw [AugmentationExtension.Complex.extendAugmentation_f_zero, augmentationZero_precomp,
    HomologicalComplex.single_map_f_self, AugmentationExtension.Complex.extendAugmentation_f_zero]
  let eY := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y
  let eZ := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Z
  let eK := K.extendXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) (i' := 0) (by simp)
  let a₀ := AugmentationExtension.Complex.augmentationZero a
  change eY.hom ≫ (u ≫ a₀) ≫ eK.inv = (eY.hom ≫ u ≫ eZ.inv) ≫ eZ.hom ≫ a₀ ≫ eK.inv
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end

end OAI.AlgebraicGeometry.Comparison.Betti.AugmentationCoefficientNormalization.ComplexExtension
