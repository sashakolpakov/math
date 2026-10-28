import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Covers -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Covers

/-!
# Affine flat surjective product covers over the actual base scheme
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

/-- Base-change and composition stability give stability under relative products of scheme morphisms. -/
theorem property_tensor (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {S : Scheme.{u}} {A B X Y : Over S} (f : A ⟶ B) (g : X ⟶ Y) (hf : P f.left) (hg : P g.left) :
    P (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap hf hg (Over.w f).symm (Over.w g).symm

variable {S : Scheme.{u}} {A B X Y : Over S} (f : A ⟶ B) (g : X ⟶ Y)

/-- The product of affine scheme morphisms is affine. -/
theorem tensorAffine [IsAffineHom f.left] [IsAffineHom g.left] : IsAffineHom (f ⊗ₘ g).left := by
  let : MorphismProperty.IsStableUnderComposition (@IsAffineHom.{u}) :=
    ⟨fun a b ha hb => by
      let := ha
      let := hb
      infer_instance⟩
  exact property_tensor (@IsAffineHom.{u}) f g inferInstance inferInstance

/-- The product of flat scheme morphisms is flat. -/
theorem tensorFlat [Flat f.left] [Flat g.left] : Flat (f ⊗ₘ g).left :=
  property_tensor (@Flat) f g inferInstance inferInstance

/-- The product of surjective scheme morphisms is surjective. -/
theorem tensorSurjective [Surjective f.left] [Surjective g.left] : Surjective (f ⊗ₘ g).left := by
  let : MorphismProperty.IsStableUnderComposition (@AlgebraicGeometry.Surjective.{u}) :=
    ⟨fun _ _ hf hg => ⟨hg.1.comp hf.1⟩⟩
  exact property_tensor (@AlgebraicGeometry.Surjective) f g inferInstance inferInstance

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Covers
