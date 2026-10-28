/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
This file has been modified.
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.MapBaseChangeHom

/-! # Free Dual Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeDualBaseChange

noncomputable section

open _root_.IsBaseChange
open _root_.Module
open _root_.Module.Dual

/- Adapted to HilbertConstruction-local declarations and default elaboration settings. -/

namespace Module.Dual

open TensorProduct LinearEquiv

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  {W : Type*} [AddCommMonoid W] [Module R W]
  (A : Type*) [CommSemiring A] [Algebra R A]

/-- Equivalent modules have equivalent duals. -/
@[simps!] def congr (e : V ≃ₗ[R] W) :
    Dual R V ≃ₗ[R] Dual R W := congrLeft R R e

/-- `LinearMap.baseChange` for `Module.Dual`. -/
def baseChange : Dual R V →ₗ[R] Dual A (A ⊗[R] V) :=
  (AlgebraTensorModule.rid R A A).compRight R ∘ₗ LinearMap.baseChangeHom R A V R

@[simp]
theorem baseChange_apply_tmul (f : Dual R V) (a : A) (v : V) :
    FreeDualBaseChange.Module.Dual.baseChange A f (a ⊗ₜ v) = (f v) • a :=
  rfl

variable {B : Type*} [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

open AlgebraTensorModule in
theorem baseChange_baseChange (f : Dual R V) :
    FreeDualBaseChange.Module.Dual.baseChange B (FreeDualBaseChange.Module.Dual.baseChange A f) =
      (congr (cancelBaseChange R A B B V)).symm (FreeDualBaseChange.Module.Dual.baseChange B f) := by
  ext; simp

end Module.Dual

namespace IsBaseChange

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.MapBaseChangeHom.IsBaseChange

open TensorProduct

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  {W : Type*} [AddCommMonoid W] [Module R W]
  {A : Type*} [CommSemiring A] [Algebra R A] [Module A W] [IsScalarTower R A W]
  {j : V →ₗ[R] W} (ibc : IsBaseChange A j)

/-- The base change of an element of the dual. -/
noncomputable def toDual :
    Dual R V →ₗ[R] Dual A W :=
  Linear.MapBaseChangeHom.IsBaseChange.linearMapLeftRightHom ibc (Algebra.linearMap R A)

theorem toDual_comp_apply (f : Dual R V) (v : V) :
    toDual ibc f (j v) = algebraMap R A (f v) := by
  simp [toDual, Linear.MapBaseChangeHom.IsBaseChange.linearMapLeftRightHom_comp_apply]

theorem toDual_apply (f : Dual R V) :
    toDual ibc f = FreeDualBaseChange.Module.Dual.congr ibc.equiv
      (FreeDualBaseChange.Module.Dual.baseChange A f) := by
  apply _root_.IsBaseChange.algHom_ext ibc
  intro v
  simp [toDual_comp_apply, Algebra.algebraMap_eq_smul_one]

/-- The linear map underlying `IsBaseChange.toDualBaseChangeLinearEquiv`. -/
private noncomputable def toDualBaseChangeAux :
    A ⊗[R] Dual R V →ₗ[A] Dual A W where
  toAddHom := (TensorProduct.lift {
    toFun a := a • toDual ibc
    map_add' a b := by simp [add_smul]
    map_smul' r a := by simp }).toAddHom
  map_smul' a g := by
    induction g using TensorProduct.inductionOn with
    | add x y hx hy => aesop
    | tmul b f => simp [TensorProduct.smul_tmul', mul_smul]

private theorem toDualBaseChangeAux_tmul (a : A) (f : Dual R V) (v : V) :
    (toDualBaseChangeAux ibc (a ⊗ₜ[R] f)) (j v) = a * algebraMap R A (f v) := by
  simp [toDualBaseChangeAux, toDual_comp_apply]

variable [Free R V] [Module.Finite R V]

/-- The linear equivalence underlying `IsBaseChange.dual`. -/
noncomputable def toDualBaseChange :
    A ⊗[R] Dual R V ≃ₗ[A] Dual A W := by
  apply LinearEquiv.ofBijective (toDualBaseChangeAux ibc)
  let b := Free.chooseBasis R V
  set ι := Free.ChooseBasisIndex R V
  have ibc_pow : IsBaseChange A ((Algebra.linearMap R A).compLeft ι) := (linearMap R A).finitePow ι
  suffices toDualBaseChangeAux ibc =
      (((b.constr R).symm.baseChange ..).trans ibc_pow.equiv).trans ((ibc.basis b).constr A) from
    this ▸ LinearEquiv.bijective _
  ext f w
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  induction w using ibc.inductionOn with
  | tmul v =>
    simp only [toDualBaseChangeAux_tmul, one_mul]
    conv_lhs => rw [← Basis.sum_equivFun b v, map_sum]
    simp [LinearEquiv.baseChange, basis_repr_comp_apply]
  | smul a w h => simp [h]
  | add x y hx hy => simp [map_add, hx, hy]

theorem toDualBaseChange_tmul (a : A) (f : Dual R V) (v : V) :
    (toDualBaseChange ibc (a ⊗ₜ[R] f)) (j v) = a * algebraMap R A (f v) :=
  toDualBaseChangeAux_tmul ibc a f v

theorem dual : IsBaseChange A (toDual ibc) := by
  apply of_equiv (toDualBaseChange ibc)
  intro f
  simp [toDualBaseChange, toDualBaseChangeAux]

end IsBaseChange

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeDualBaseChange
