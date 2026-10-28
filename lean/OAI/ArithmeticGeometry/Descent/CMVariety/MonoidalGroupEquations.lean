import Mathlib.CategoryTheory.Monoidal.Mon

/-! # Monoidal Group Equations -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.MonoidalGroupEquations.Abelian

noncomputable section

/-!
A morphism after monoidal base change preserves the group structure
exactly when the images of the original unit and multiplication equations
hold. This exposes the two finite equations to the spreading theorem.
-/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem isMonHom_map_iff_image_equations
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) :
    IsMonHom (F.map f) ↔
      F.map (η[A] ≫ f) = F.map η[B] ∧
      F.map (μ[A] ≫ f) = F.map ((f ⊗ₘ f) ≫ μ[B]) := by
  have hu : (η[F.obj A] ≫ F.map f = η[F.obj B]) ↔
      F.map (η[A] ≫ f) = F.map η[B] := by
    change (Functor.LaxMonoidal.ε F ≫ F.map η[A]) ≫ F.map f =
      Functor.LaxMonoidal.ε F ≫ F.map η[B] ↔ _
    rw [Category.assoc, ← F.map_comp, cancel_epi]
  have hm : (μ[F.obj A] ≫ F.map f = (F.map f ⊗ₘ F.map f) ≫ μ[F.obj B]) ↔
      F.map (μ[A] ≫ f) = F.map ((f ⊗ₘ f) ≫ μ[B]) := by
    change (Functor.LaxMonoidal.μ F A A ≫ F.map μ[A]) ≫ F.map f =
      (F.map f ⊗ₘ F.map f) ≫ (Functor.LaxMonoidal.μ F B B ≫ F.map μ[B]) ↔ _
    rw [Category.assoc, ← F.map_comp, Functor.LaxMonoidal.μ_natural_assoc,
      ← F.map_comp, cancel_epi]
  constructor
  · intro h
    exact ⟨hu.mp (IsMonHom.one_hom (F.map f)), hm.mp (IsMonHom.mul_hom (F.map f))⟩
  · rintro ⟨hunit, hmul⟩
    exact ⟨hu.mpr hunit, hm.mpr hmul⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.MonoidalGroupEquations.Abelian
