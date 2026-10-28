import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMonoidAxes
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Pointed Multiplication Unit -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMultiplicationUnit

noncomputable section

/-! The two maps whose equality expresses multiplication preservation are pointed whenever the original map is pointed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem pointedMultiplicationComposites_preserve_unit {S : Scheme.{u}} {A B : Over S}
    [GrpObj A] [GrpObj B] (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) :
    (η[A ⊗ A] ≫ (μ[A] ≫ f) = η[B]) ∧
      (η[A ⊗ A] ≫ ((f ⊗ₘ f) ≫ μ[B]) = η[B]) := by
  let l : A ⟶ A ⊗ A := lift (𝟙 A) (1 : A ⟶ A)
  have : IsMonHom (1 : A ⟶ A) := by
    change IsMonHom (toUnit A ≫ η[A])
    infer_instance
  have : IsMonHom l := inferInstanceAs (IsMonHom (lift (𝟙 A) (1 : A ⟶ A)))
  have hl : η[A] ≫ l = η[A ⊗ A] := IsMonHom.one_hom l
  have hmul : l ≫ μ[A] = 𝟙 A := PointedMonoidAxes.monoid_mul_right_axis A
  have h₁ : l ≫ (μ[A] ≫ f) = f := by rw [← Category.assoc, hmul, Category.id_comp]
  have h₂ : l ≫ ((f ⊗ₘ f) ≫ μ[B]) = f := PointedMonoidAxes.pointed_mul_right_axis A B f hf
  constructor
  · rw [← hl, Category.assoc, h₁]
    exact hf
  · rw [← hl, Category.assoc, h₂]
    exact hf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMultiplicationUnit
