import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UnitOperations

/-! # Reduction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Reduction.CM

noncomputable section

/-! Elementary row reduction in SL3 over a local coefficient ring.
The unit pivots and all normalizing matrices are constructed explicitly. -/

open scoped Classical _root_.Matrix
open _root_.Matrix _root_.Matrix.SpecialLinearGroup
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Pivots.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UnitOperations.CM

variable {R : Type*} [CommRing R]
  (S : Subgroup (SpecialLinearGroup (Fin 3) R))
  (hS : ∀ (i j : Fin 3) (hij : i ≠ j) (a : R), SpecialLinearGroup.transvection hij a ∈ S)

include hS

theorem first_unit (g : SpecialLinearGroup (Fin 3) R) (u : Rˣ) (hu : g.val 0 0 = (u : R)) :
    ∃ A ∈ S, (A * g).val 0 0 = 1 ∧ (A * g).val 1 0 = 0 ∧ (A * g).val 2 0 = 0 := by
  let U := transvection (show (2 : Fin 3) ≠ 0 by decide) (-g.val 2 0 * (u⁻¹ : Rˣ)) *
    transvection (show (1 : Fin 3) ≠ 0 by decide) (-g.val 1 0 * (u⁻¹ : Rˣ))
  let D := UnitOperations.CM.scaling (show (0 : Fin 3) ≠ 1 by decide) u⁻¹
  have hU : U ∈ S := S.mul_mem (hS _ _ _ _) (hS _ _ _ _)
  refine ⟨D * U, S.mul_mem (UnitOperations.CM.scaling_mem S hS _ _) hU, ?_, ?_, ?_⟩
  · rw [mul_assoc, UnitOperations.CM.scaling_row_first]
    simp [U, mul_assoc, Pivots.CM.row_add, hu]
  · rw [mul_assoc, UnitOperations.CM.scaling_row_second]
    simp [U, mul_assoc, Pivots.CM.row_add, hu]
  · rw [mul_assoc, UnitOperations.CM.scaling_row_other (show (0 : Fin 3) ≠ 1 by decide) u⁻¹
      (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
    simp [U, mul_assoc, Pivots.CM.row_add, hu]

variable [IsLocalRing R]

theorem first_column (g : SpecialLinearGroup (Fin 3) R) :
    ∃ A ∈ S, (A * g).val 0 0 = 1 ∧ (A * g).val 1 0 = 0 ∧ (A * g).val 2 0 = 0 := by
  obtain ⟨i, hi⟩ := Pivots.CM.column_has_unit g 0
  fin_cases i
  · exact first_unit S hS g hi.unit hi.unit_spec.symm
  · let W := UnitOperations.CM.rotation (show (0 : Fin 3) ≠ 1 by decide) (1 : Rˣ)
    have hW : (W * g).val 0 0 = (hi.unit : R) := by
      rw [UnitOperations.CM.rotation_row_first, Units.val_one, one_mul, hi.unit_spec]
      rfl
    obtain ⟨A, hA, h⟩ := first_unit S hS (W * g) hi.unit hW
    exact ⟨A * W, S.mul_mem hA (UnitOperations.CM.rotation_mem S hS _ _), by simpa only [mul_assoc] using h⟩
  · let W := UnitOperations.CM.rotation (show (0 : Fin 3) ≠ 2 by decide) (1 : Rˣ)
    have hW : (W * g).val 0 0 = (hi.unit : R) := by
      rw [UnitOperations.CM.rotation_row_first, Units.val_one, one_mul, hi.unit_spec]
      rfl
    obtain ⟨A, hA, h⟩ := first_unit S hS (W * g) hi.unit hW
    exact ⟨A * W, S.mul_mem hA (UnitOperations.CM.rotation_mem S hS _ _), by simpa only [mul_assoc] using h⟩

omit S hS in
theorem lower_unit (g : SpecialLinearGroup (Fin 3) R)
    (h00 : g.val 0 0 = 1) (h10 : g.val 1 0 = 0) (h20 : g.val 2 0 = 0) :
    IsUnit (g.val 1 1) ∨ IsUnit (g.val 2 1) := by
  have hd : g.val 1 1 * g.val 2 2 - g.val 1 2 * g.val 2 1 = 1 := by
    have hdet := g.property
    rw [Matrix.det_fin_three] at hdet
    simpa only [h00, h10, h20, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero] using hdet
  have hsum : IsUnit (g.val 1 1 * g.val 2 2 + (-g.val 1 2) * g.val 2 1) := by
    rw [neg_mul, ← sub_eq_add_neg, hd]
    exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with h | h
  · exact Or.inl (isUnit_of_mul_isUnit_left h)
  · exact Or.inr (isUnit_of_mul_isUnit_right h)

omit [IsLocalRing R] in
theorem second_unit (g : SpecialLinearGroup (Fin 3) R)
    (h00 : g.val 0 0 = 1) (h10 : g.val 1 0 = 0) (h20 : g.val 2 0 = 0)
    (u : Rˣ) (hu : g.val 1 1 = (u : R)) :
    ∃ A ∈ S, (A * g).val 0 0 = 1 ∧ (A * g).val 1 0 = 0 ∧ (A * g).val 2 0 = 0 ∧
      (A * g).val 1 1 = 1 ∧ (A * g).val 2 1 = 0 := by
  let U := transvection (show (2 : Fin 3) ≠ 1 by decide) (-g.val 2 1 * (u⁻¹ : Rˣ))
  let D := UnitOperations.CM.scaling (show (1 : Fin 3) ≠ 2 by decide) u⁻¹
  refine ⟨D * U, S.mul_mem (UnitOperations.CM.scaling_mem S hS _ _) (hS _ _ _ _), ?_, ?_, ?_, ?_, ?_⟩
  · rw [mul_assoc, UnitOperations.CM.scaling_row_other (show (1 : Fin 3) ≠ 2 by decide) u⁻¹
      (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)]
    simp [U, Pivots.CM.row_add, h00]
  · rw [mul_assoc, UnitOperations.CM.scaling_row_first]
    simp [U, Pivots.CM.row_add, h10]
  · rw [mul_assoc, UnitOperations.CM.scaling_row_second]
    simp [U, Pivots.CM.row_add, h10, h20]
  · rw [mul_assoc, UnitOperations.CM.scaling_row_first]
    simp [U, Pivots.CM.row_add, hu]
  · rw [mul_assoc, UnitOperations.CM.scaling_row_second]
    simp [U, Pivots.CM.row_add, hu, mul_assoc]

theorem first_two_columns (g : SpecialLinearGroup (Fin 3) R) :
    ∃ A ∈ S, (A * g).val 0 0 = 1 ∧ (A * g).val 1 0 = 0 ∧ (A * g).val 2 0 = 0 ∧
      (A * g).val 1 1 = 1 ∧ (A * g).val 2 1 = 0 := by
  obtain ⟨A, hA, h00, h10, h20⟩ := first_column S hS g
  rcases lower_unit (A * g) h00 h10 h20 with hu | hu
  · obtain ⟨D, hD, h⟩ := second_unit S hS (A * g) h00 h10 h20 hu.unit hu.unit_spec.symm
    exact ⟨D * A, S.mul_mem hD hA, by simpa only [mul_assoc] using h⟩
  · let W := UnitOperations.CM.rotation (show (1 : Fin 3) ≠ 2 by decide) (1 : Rˣ)
    have h00' : (W * (A * g)).val 0 0 = 1 := by
      rw [UnitOperations.CM.rotation_row_other _ _ (by decide : (0 : Fin 3) ≠ 1)
        (by decide : (0 : Fin 3) ≠ 2), h00]
    have h10' : (W * (A * g)).val 1 0 = 0 := by rw [UnitOperations.CM.rotation_row_first, h20, mul_zero]
    have h20' : (W * (A * g)).val 2 0 = 0 := by rw [UnitOperations.CM.rotation_row_second, h10, mul_zero]
    have hu' : (W * (A * g)).val 1 1 = (hu.unit : R) := by
      rw [UnitOperations.CM.rotation_row_first, Units.val_one, one_mul, hu.unit_spec]
    obtain ⟨D, hD, h⟩ := second_unit S hS (W * (A * g)) h00' h10' h20' hu.unit hu'
    exact ⟨D * W * A, S.mul_mem (S.mul_mem hD (UnitOperations.CM.rotation_mem S hS _ _)) hA,
      by simpa only [mul_assoc] using h⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Reduction.CM
