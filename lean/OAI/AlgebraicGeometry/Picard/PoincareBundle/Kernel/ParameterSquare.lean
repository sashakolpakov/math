import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Covers
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Parameter Square -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ParameterSquare

noncomputable section

/-! The actual family square obtained by fixing a subgroup parameter and quotienting the second coordinate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S : Scheme.{u}} {H A B : Over S} (h : H ⟶ A) (f : A ⟶ B)

/-- The family cover retains the entire subgroup parameter scheme. -/
def cover : H ⊗ A ⟶ H ⊗ B := 𝟙 H ⊗ₘ f

/-- The actual source point of the original product family. -/
def source : H ⊗ A ⟶ A ⊗ A := h ⊗ₘ 𝟙 A

/-- The actual target point of the quotient product family. -/
def target : H ⊗ B ⟶ B ⊗ B := (h ≫ f) ⊗ₘ 𝟙 B

/-- Fixing the subgroup coordinate commutes with quotienting both original coordinates. -/
theorem square : source h ≫ (f ⊗ₘ f) = cover (H := H) f ≫ target h f := by
  dsimp only [source, cover, target]
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.id_comp,
    Category.id_comp, Category.comp_id]

/-- The full family cover is affine, flat and surjective under the original quotient hypotheses. -/
theorem affine_flat_surjective [IsAffineHom f.left] [Flat f.left] [Surjective f.left] :
    IsAffineHom (cover (H := H) f).left ∧ Flat (cover (H := H) f).left ∧
      Surjective (cover (H := H) f).left := by
  have : IsIso (𝟙 H : H ⟶ H).left := inferInstanceAs (IsIso (𝟙 H.left))
  exact ⟨Product.Covers.tensorAffine (𝟙 H) f, Product.Covers.tensorFlat (𝟙 H) f,
    Product.Covers.tensorSurjective (𝟙 H) f⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ParameterSquare
