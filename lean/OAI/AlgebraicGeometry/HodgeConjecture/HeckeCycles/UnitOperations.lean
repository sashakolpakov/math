import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Pivots

/-! # Unit Operations -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UnitOperations.CM

noncomputable section

/-! Unit row rotations and pair scalings as explicit products of
elementary SL3 matrices over the original coefficient ring. -/

open scoped Classical _root_.Matrix
open _root_.Matrix _root_.Matrix.SpecialLinearGroup
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Pivots.CM

variable {R : Type*} [CommRing R]

def rotation {i j : Fin 3} (hij : i ≠ j) (u : Rˣ) : SpecialLinearGroup (Fin 3) R :=
  transvection hij (u : R) * transvection hij.symm (-(u⁻¹ : Rˣ) : R) * transvection hij (u : R)

theorem rotation_row_first {i j : Fin 3} (hij : i ≠ j) (u : Rˣ)
    (g : SpecialLinearGroup (Fin 3) R) (c : Fin 3) :
    (rotation hij u * g).val i c = (u : R) * g.val j c := by
  have hunit : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.val_inv
  simp only [rotation, mul_assoc, Local.Pivots.CM.row_add, ite_true, ite_eq_right hij, ite_eq_right hij.symm]
  linear_combination -(g.val i c + (u : R) * g.val j c) * hunit

theorem rotation_row_second {i j : Fin 3} (hij : i ≠ j) (u : Rˣ)
    (g : SpecialLinearGroup (Fin 3) R) (c : Fin 3) :
    (rotation hij u * g).val j c = -(u⁻¹ : Rˣ) * g.val i c := by
  have hunit : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := u.inv_val
  simp only [rotation, mul_assoc, Local.Pivots.CM.row_add, ite_true, ite_eq_right hij.symm, add_zero]
  linear_combination -g.val j c * hunit

theorem rotation_row_other {i j r : Fin 3} (hij : i ≠ j) (u : Rˣ)
    (hri : r ≠ i) (hrj : r ≠ j) (g : SpecialLinearGroup (Fin 3) R) (c : Fin 3) :
    (rotation hij u * g).val r c = g.val r c := by
  simp only [rotation, mul_assoc, Local.Pivots.CM.row_add, ite_eq_right hri, ite_eq_right hrj, add_zero]

def scaling {i j : Fin 3} (hij : i ≠ j) (u : Rˣ) : SpecialLinearGroup (Fin 3) R :=
  rotation hij u * rotation hij (-1)

theorem scaling_row_first {i j : Fin 3} (hij : i ≠ j) (u : Rˣ)
    (g : SpecialLinearGroup (Fin 3) R) (c : Fin 3) :
    (scaling hij u * g).val i c = (u : R) * g.val i c := by
  rw [scaling, mul_assoc, rotation_row_first, rotation_row_second]
  simp

theorem scaling_row_second {i j : Fin 3} (hij : i ≠ j) (u : Rˣ)
    (g : SpecialLinearGroup (Fin 3) R) (c : Fin 3) :
    (scaling hij u * g).val j c = (u⁻¹ : Rˣ) * g.val j c := by
  rw [scaling, mul_assoc, rotation_row_second, rotation_row_first]
  simp

theorem scaling_row_other {i j r : Fin 3} (hij : i ≠ j) (u : Rˣ)
    (hri : r ≠ i) (hrj : r ≠ j) (g : SpecialLinearGroup (Fin 3) R) (c : Fin 3) :
    (scaling hij u * g).val r c = g.val r c := by
  rw [scaling, mul_assoc, rotation_row_other hij u hri hrj,
    rotation_row_other hij (-1) hri hrj]

theorem rotation_mem (S : Subgroup (SpecialLinearGroup (Fin 3) R))
    (hS : ∀ (i j : Fin 3) (hij : i ≠ j) (a : R), SpecialLinearGroup.transvection hij a ∈ S)
    {i j : Fin 3} (hij : i ≠ j) (u : Rˣ) : rotation hij u ∈ S :=
  S.mul_mem (S.mul_mem (hS _ _ _ _) (hS _ _ _ _)) (hS _ _ _ _)

theorem scaling_mem (S : Subgroup (SpecialLinearGroup (Fin 3) R))
    (hS : ∀ (i j : Fin 3) (hij : i ≠ j) (a : R), SpecialLinearGroup.transvection hij a ∈ S)
    {i j : Fin 3} (hij : i ≠ j) (u : Rˣ) : scaling hij u ∈ S :=
  S.mul_mem (rotation_mem S hS hij u) (rotation_mem S hS hij (-1))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UnitOperations.CM
