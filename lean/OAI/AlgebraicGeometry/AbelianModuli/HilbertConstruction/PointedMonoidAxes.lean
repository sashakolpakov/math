import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-! # Pointed Monoid Axes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMonoidAxes

noncomputable section

/-! Identity-preserving maps respect multiplication on each identity axis. -/

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable (G H : C) [MonObj G] [MonObj H]

theorem monoid_mul_right_axis : lift (𝟙 G) (toUnit G ≫ η[G]) ≫ μ[G] = 𝟙 G :=
  mul_one (𝟙 G)

theorem monoid_mul_left_axis : lift (toUnit G ≫ η[G]) (𝟙 G) ≫ μ[G] = 𝟙 G :=
  one_mul (𝟙 G)

theorem pointed_mul_right_axis (f : G ⟶ H) (hf : η[G] ≫ f = η[H]) :
    lift (𝟙 G) (toUnit G ≫ η[G]) ≫ (f ⊗ₘ f) ≫ μ[H] = f := by
  rw [lift_map_assoc, Category.id_comp, Category.assoc, hf]
  exact mul_one f

theorem pointed_mul_left_axis (f : G ⟶ H) (hf : η[G] ≫ f = η[H]) :
    lift (toUnit G ≫ η[G]) (𝟙 G) ≫ (f ⊗ₘ f) ≫ μ[H] = f := by
  rw [lift_map_assoc, Category.id_comp, Category.assoc, hf]
  exact one_mul f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMonoidAxes
