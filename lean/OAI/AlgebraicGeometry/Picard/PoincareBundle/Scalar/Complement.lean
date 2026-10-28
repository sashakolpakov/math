import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Complement -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.Complement

/-! Scalar complementary identities imply finiteness and surjectivity of actual scheme maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {B D : Over S} [GrpObj B] [GrpObj D]
  (m : B ⟶ D) (r : D ⟶ B) (n : ℕ)

omit [GrpObj D] in
/-- A finite scalar composition makes the original map finite when its complementary map is separated. -/
theorem finite_of_scalar_complement (h : m ≫ r = (𝟙 B) ^ n)
    [IsFinite ((𝟙 B) ^ n).left] [IsSeparated r.left] : IsFinite m.left := by
  have hh : m.left ≫ r.left = ((𝟙 B) ^ n).left := congrArg Over.Hom.left h
  have : IsFinite (m.left ≫ r.left) := by rw [hh]; infer_instance
  exact IsFinite.of_comp m.left r.left

omit [GrpObj B] in
/-- Surjectivity of the opposite scalar composition makes the original map surjective. -/
theorem surjective_of_scalar_complement (h : r ≫ m = (𝟙 D) ^ n)
    [Surjective ((𝟙 D) ^ n).left] : Surjective m.left := by
  have hh : r.left ≫ m.left = ((𝟙 D) ^ n).left := congrArg Over.Hom.left h
  have : Surjective (r.left ≫ m.left) := by rw [hh]; infer_instance
  exact Surjective.of_comp r.left m.left

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.Complement
