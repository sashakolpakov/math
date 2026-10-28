import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Monoidal Scalar Preservation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.MonoidalScalarPreservation

/-! Strong cartesian monoidal functors preserve actual integer multiplication maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v u' v'

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- Preservation of products gives preservation of pointwise powers. -/
theorem map_pow {X Y : C} [MonObj Y] (f : X ⟶ Y) (n : ℕ) : F.map (f ^ n) = (F.map f) ^ n :=
  (F.homMonoidHom).map_pow f n

/-- Integer multiplication on a group object commutes with this functor. -/
theorem map_scalar (X : C) [MonObj X] (n : ℕ) : F.map ((𝟙 X) ^ n) = (𝟙 (F.obj X)) ^ n :=
  (MonoidalScalarPreservation.map_pow F (𝟙 X) n).trans (congrArg (fun t => t ^ n) (F.map_id X))

end OAI.AlgebraicGeometry.Picard.PoincareBundle.MonoidalScalarPreservation
