import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.QuasiIso

/-! # Quasi Iso Right -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.QuasiIsoRight.QuasiIsoFunctorComposition

/-! A typed cancellation interface for quasi-isomorphisms of images
under a complex-valued functor. -/

open _root_.CategoryTheory

universe u v w z
variable {C : Type u} [Category.{v} C] {A : Type w} [Category.{z} A] [Abelian A]
  {α : Type*} {c : ComplexShape α} (F : C ⥤ HomologicalComplex A c)
  {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z)

theorem right (ha : QuasiIso (F.map a)) (hab : QuasiIso (F.map (a ≫ b))) : QuasiIso (F.map b) := by
  have h := (F.map_comp a b) ▸ hab
  exact (quasiIso_iff_comp_left _ _ (hφ := ha)).mp h

end OAI.NumberTheory.PadicHodge.GeometricComparison.QuasiIsoRight.QuasiIsoFunctorComposition
