import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Monoidal Reduction Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MonoidalReductionMultiplication

/-! A monoidal image that preserves group multiplication makes the
original multiplication square commute after applying that functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {C D : Type*} [Category* C] [Category* D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {A B : C} [GrpObj A] [GrpObj B]

theorem monoidalMap_multiplication_of_isMonHom (f : A ⟶ B) [IsMonHom (F.map f)] :
    F.map (μ[A] ≫ f) = F.map ((f ⊗ₘ f) ≫ μ[B]) := by
  apply (cancel_epi (Functor.LaxMonoidal.μ F A A)).mp
  calc
    Functor.LaxMonoidal.μ F A A ≫ F.map (μ[A] ≫ f) = μ[F.obj A] ≫ F.map f := by
      rw [Functor.map_comp]
      exact (Category.assoc _ _ _).symm
    _ = (F.map f ⊗ₘ F.map f) ≫ μ[F.obj B] := IsMonHom.mul_hom (F.map f)
    _ = Functor.LaxMonoidal.μ F A A ≫ F.map (f ⊗ₘ f) ≫ F.map μ[B] := by
      change (F.map f ⊗ₘ F.map f) ≫ (Functor.LaxMonoidal.μ F B B ≫ F.map μ[B]) = _
      rw [← Category.assoc, Functor.LaxMonoidal.μ_natural, Category.assoc]
    _ = Functor.LaxMonoidal.μ F A A ≫ F.map ((f ⊗ₘ f) ≫ μ[B]) := by rw [Functor.map_comp]

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MonoidalReductionMultiplication
