import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Pointed Tensor Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointedTensorIsomorphism

/-! A pointed carrier isomorphism has a pointed inverse and pointed
product isomorphism, without presupposing multiplication compatibility. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {A B : C} [GrpObj A] [GrpObj B]

omit [BraidedCategory C] in
theorem pointedIso_inverse (e : A ≅ B) (he : η[A] ≫ e.hom = η[B]) : η[B] ≫ e.inv = η[A] := by
  rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem pointedHom_tensor (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) :
    η[A ⊗ A] ≫ (f ⊗ₘ f) = η[B ⊗ B] := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tensorHom_fst, ← Category.assoc, IsMonHom.one_hom (fst A A),
      IsMonHom.one_hom (fst B B), hf]
  · rw [Category.assoc, tensorHom_snd, ← Category.assoc, IsMonHom.one_hom (snd A A),
      IsMonHom.one_hom (snd B B), hf]

theorem pointedIso_tensor_inverse (e : A ≅ B) (he : η[A] ≫ e.hom = η[B]) :
    η[B ⊗ B] ≫ (e ⊗ᵢ e).inv = η[A ⊗ A] :=
  pointedHom_tensor e.inv (pointedIso_inverse e he)

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointedTensorIsomorphism
