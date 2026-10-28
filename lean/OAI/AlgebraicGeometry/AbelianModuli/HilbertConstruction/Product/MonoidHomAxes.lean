import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMonoidAxes

/-! # Monoid Hom Axes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.MonoidHomAxes

noncomputable section

/-! A monoid homomorphism from a product is determined by its restrictions to the two identity axes. -/

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe v u

theorem productMonoidHom_eq_of_axes
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
    (G B H : C) [MonObj G] [MonObj B] [MonObj H]
    (f q : G ⊗ B ⟶ H) [IsMonHom f] [IsMonHom q]
    (hr : lift (𝟙 G) (1 : G ⟶ B) ≫ f = lift (𝟙 G) (1 : G ⟶ B) ≫ q)
    (hl : lift (1 : B ⟶ G) (𝟙 B) ≫ f = lift (1 : B ⟶ G) (𝟙 B) ≫ q) : f = q := by
  let a := fst G B ≫ lift (𝟙 G) (1 : G ⟶ B)
  let b := snd G B ≫ lift (1 : B ⟶ G) (𝟙 B)
  have hab : a * b = 𝟙 (G ⊗ B) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [MonObj.mul_comp, a, b]
    · simp [MonObj.mul_comp, a, b]
  have h₁ : a ≫ f = a ≫ q := by simpa only [a, Category.assoc] using congrArg (fun z => fst G B ≫ z) hr
  have h₂ : b ≫ f = b ≫ q := by simpa only [b, Category.assoc] using congrArg (fun z => snd G B ≫ z) hl
  calc
    f = (a * b) ≫ f := by rw [hab, Category.id_comp]
    _ = (a ≫ f) * (b ≫ f) := MonObj.mul_comp a b f
    _ = (a ≫ q) * (b ≫ q) := congrArg₂ (fun x y => x * y) h₁ h₂
    _ = (a * b) ≫ q := (MonObj.mul_comp a b q).symm
    _ = q := by rw [hab, Category.id_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.MonoidHomAxes
