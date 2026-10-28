import Mathlib.CategoryTheory.Monoidal.Mon

/-! # Monoid Hom Epi Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidHomEpiDescent

noncomputable section

/-! The monoid-homomorphism equations descend when the covering map on products is an epimorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v

theorem isMonHom_of_tensor_epi {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {X Y Z : C} [MonObj X] [MonObj Y] [MonObj Z]
    (f : X ⟶ Y) (m : X ⟶ Z) (d : Y ⟶ Z) [IsMonHom f] [IsMonHom m]
    [Epi (f ⊗ₘ f)] (hd : f ≫ d = m) : IsMonHom d where
  one_hom := by
    calc
      η[Y] ≫ d = (η[X] ≫ f) ≫ d := congrArg (fun a => a ≫ d) (IsMonHom.one_hom f).symm
      _ = η[X] ≫ m := (Category.assoc _ _ _).trans (congrArg (fun a => η[X] ≫ a) hd)
      _ = η[Z] := IsMonHom.one_hom m
  mul_hom := by
    apply (cancel_epi (f ⊗ₘ f)).mp
    calc
      (f ⊗ₘ f) ≫ μ[Y] ≫ d = (μ[X] ≫ f) ≫ d :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ d) (IsMonHom.mul_hom f).symm)
      _ = μ[X] ≫ m := (Category.assoc _ _ _).trans (congrArg (fun a => μ[X] ≫ a) hd)
      _ = (m ⊗ₘ m) ≫ μ[Z] := IsMonHom.mul_hom m
      _ = ((f ≫ d) ⊗ₘ (f ≫ d)) ≫ μ[Z] := congrArg (fun a => (a ⊗ₘ a) ≫ μ[Z]) hd.symm
      _ = (f ⊗ₘ f) ≫ (d ⊗ₘ d) ≫ μ[Z] := by
        rw [← tensorHom_comp_tensorHom, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidHomEpiDescent
