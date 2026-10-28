import Mathlib.CategoryTheory.Monoidal.Category

/-! # Tensor Comultiplication -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorComultiplication

/-! Coassociativity for tensor products of morphisms from a unit object. -/

open _root_.CategoryTheory MonoidalCategory
universe u v
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

theorem tensorIso_inv_coassoc {O : D} (m : O ⊗ O ≅ O)
    (h : (α_ O O O).inv ≫ (m.hom ⊗ₘ 𝟙 O) ≫ m.hom =
      (𝟙 O ⊗ₘ m.hom) ≫ m.hom) :
    m.inv ≫ (m.inv ⊗ₘ 𝟙 O) ≫ (α_ O O O).hom =
      m.inv ≫ (𝟙 O ⊗ₘ m.inv) := by
  have hi : m.symm ≪≫ (m.symm ⊗ᵢ Iso.refl O) ≪≫ α_ O O O =
      m.symm ≪≫ (Iso.refl O ⊗ᵢ m.symm) := by
    apply Iso.ext_inv
    simpa only [Iso.trans_inv, Iso.symm_inv, tensorIso_inv, Iso.refl_inv,
      Category.assoc] using h
  exact congrArg Iso.hom hi

theorem tensorComulHom_assoc {A B C O : D}
    (a : O ⟶ A) (b : O ⟶ B) (c : O ⟶ C) (comul : O ⟶ O ⊗ O)
    (h : comul ≫ (comul ⊗ₘ 𝟙 O) ≫ (α_ O O O).hom =
      comul ≫ (𝟙 O ⊗ₘ comul)) :
    comul ≫ ((comul ≫ (a ⊗ₘ b)) ⊗ₘ c) ≫ (α_ A B C).hom =
      comul ≫ (a ⊗ₘ (comul ≫ (b ⊗ₘ c))) := by
  have hleft : ((comul ≫ (a ⊗ₘ b)) ⊗ₘ c) =
      (comul ⊗ₘ 𝟙 O) ≫ ((a ⊗ₘ b) ⊗ₘ c) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  have hright : (a ⊗ₘ (comul ≫ (b ⊗ₘ c))) =
      (𝟙 O ⊗ₘ comul) ≫ (a ⊗ₘ (b ⊗ₘ c)) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  rw [hleft, Category.assoc, associator_naturality]
  simpa only [Category.assoc, ← hright] using
    congrArg (fun f => f ≫ (a ⊗ₘ (b ⊗ₘ c))) h

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorComultiplication
