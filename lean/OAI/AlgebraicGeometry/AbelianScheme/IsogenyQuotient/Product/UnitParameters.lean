import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

/-! # Unit Parameters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.UnitParameters.Construction

noncomputable section

/-! Universal unit configurations on a product of group schemes, with
exact factorization for every test-scheme unit configuration. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u
variable {S : Scheme.{u}} (A B : Over S) [GrpObj A] [GrpObj B]

def productHorizontalUnitParameter : A ⊗ B ⟶ A ⊗ B :=
  lift (1 : A ⊗ B ⟶ A) (snd A B)

def productVerticalUnitParameter : A ⊗ B ⟶ A ⊗ B :=
  lift (fst A B) (1 : A ⊗ B ⟶ B)

instance productHorizontalUnitParameter_isMonHom : IsMonHom (productHorizontalUnitParameter A B) := by
  unfold productHorizontalUnitParameter
  rw [Hom.one_def]
  infer_instance

instance productVerticalUnitParameter_isMonHom : IsMonHom (productVerticalUnitParameter A B) := by
  unfold productVerticalUnitParameter
  rw [Hom.one_def]
  infer_instance

omit [GrpObj B] in
theorem productHorizontalUnitParameter_first : productHorizontalUnitParameter A B ≫ fst A B = 1 :=
  lift_fst _ _

omit [GrpObj A] in
theorem productVerticalUnitParameter_second : productVerticalUnitParameter A B ≫ snd A B = 1 :=
  lift_snd _ _

omit [GrpObj B] in
theorem productHorizontalUnitParameter_relation :
    Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst A B) (snd A B)
      (productHorizontalUnitParameter A B) (𝟙 _) (𝟙 _) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [productHorizontalUnitParameter, lift_fst, Category.id_comp, one_mul]
  · simp only [productHorizontalUnitParameter, lift_snd, Category.id_comp]
  · simp only [productHorizontalUnitParameter, lift_snd, Category.id_comp]

omit [GrpObj A] in
theorem productVerticalUnitParameter_relation :
    Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd A B) (fst A B)
      (productVerticalUnitParameter A B) (𝟙 _) (𝟙 _) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [productVerticalUnitParameter, lift_snd, Category.id_comp, one_mul]
  · simp only [productVerticalUnitParameter, lift_fst, Category.id_comp]
  · simp only [productVerticalUnitParameter, lift_fst, Category.id_comp]

omit [GrpObj B] in
theorem productHorizontalUnitParameter_factor {T : Over S} (a x : T ⟶ A ⊗ B)
    (ha : a ≫ fst A B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst A B) (snd A B) a x x) :
    x ≫ productHorizontalUnitParameter A B = a := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [productHorizontalUnitParameter, Category.assoc, lift_fst, MonObj.comp_one] using ha.symm
  · simpa only [productHorizontalUnitParameter, Category.assoc, lift_snd] using h.2.1.symm

omit [GrpObj A] in
theorem productVerticalUnitParameter_factor {T : Over S} (a x : T ⟶ A ⊗ B)
    (ha : a ≫ snd A B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd A B) (fst A B) a x x) :
    x ≫ productVerticalUnitParameter A B = a := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [productVerticalUnitParameter, Category.assoc, lift_fst] using h.2.1.symm
  · simpa only [productVerticalUnitParameter, Category.assoc, lift_snd, MonObj.comp_one] using ha.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.UnitParameters.Construction
