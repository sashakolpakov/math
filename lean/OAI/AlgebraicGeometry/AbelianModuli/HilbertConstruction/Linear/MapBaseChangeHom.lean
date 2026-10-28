/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
This file has been modified.
-/
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-! # Map Base Change Hom -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.MapBaseChangeHom.IsBaseChange

open _root_.IsBaseChange

open LinearMap TensorProduct _root_.Module

variable {R : Type*} [CommSemiring R]
    {S : Type*} [CommSemiring S] [Algebra R S]
    {M : Type*} [AddCommMonoid M] [Module R M]
    {N : Type*} [AddCommMonoid N] [Module R N]
    {P : Type*} [AddCommMonoid P] [Module R P]

variable
  {Q : Type*} [AddCommMonoid Q] [Module R Q]
  [Module S P] [IsScalarTower R S P]
  [Module S Q] [IsScalarTower R S Q]

/-- The base change map for linear maps with source a free finite module. -/
noncomputable def linearMapLeftRightHom {α : M →ₗ[R] P} (j : IsBaseChange S α)
    (β : N →ₗ[R] Q) :
    (M →ₗ[R] N) →ₗ[R] (P →ₗ[S] Q) :=
  ((LinearMap.llcomp (σ₂₃ := RingHom.id S) S P (S ⊗[R] M) Q).flip
    j.equiv.symm.toLinearMap) ∘ₗ
    (liftBaseChangeEquiv S).toLinearMap.restrictScalars R ∘ₗ
      (compRight R β (M := M))

theorem linearMapLeftRightHom_apply
    {α : M →ₗ[R] P} (j : IsBaseChange S α) (β : N →ₗ[R] Q) (f : M →ₗ[R] N) (p : P) :
    linearMapLeftRightHom j β f p = ((liftBaseChangeEquiv S) (β ∘ₗ f)) (j.equiv.symm p) := by
  rfl

@[simp] theorem linearMapLeftRightHom_comp_apply
    {α : M →ₗ[R] P} (j : IsBaseChange S α) (β : N →ₗ[R] Q) (f : M →ₗ[R] N) (m : M) :
    linearMapLeftRightHom j β f (α m) = β (f m) := by
  simp [linearMapLeftRightHom_apply, IsBaseChange.equiv_symm_apply]

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.MapBaseChangeHom.IsBaseChange
