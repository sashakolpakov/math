/-
Discussions and model prompting: Alexander Kolpakov (UATX).

Source: sashakolpakov/spherical-regge-scissors, commit
d40eb8990bcf1ba5525435f8517e9ba5c202b549.
-/

import Mathlib

/-!
# The four-variable Regge matrix

This file checks the finite-dimensional linear algebra used in Sections 2
and 4 of the manuscript.  The index type `Four` is the ordered list of the
four moving edges.  The matrix `reggeMatrix` is

`R = (1 / 2) J - I`,

and `hadamardMatrix = 2 R` is the integral sign matrix used after choosing
half-phases.
-/

namespace SphericalReggeScissors

abbrev Four := Fin 4

/-- The Regge involution `R = (1 / 2) J - I` on the four moving entries. -/
def reggeMatrix : Matrix Four Four ℚ :=
  fun i j => (1 / 2 : ℚ) - if i = j then 1 else 0

/-- The integral matrix `H = 2 R = J - 2 I`. -/
def hadamardMatrix : Matrix Four Four ℚ :=
  fun i j => if i = j then -1 else 1

@[simp]
theorem reggeMatrix_apply (i j : Four) :
    reggeMatrix i j = (1 / 2 : ℚ) - if i = j then 1 else 0 := rfl

@[simp]
theorem hadamardMatrix_apply (i j : Four) :
    hadamardMatrix i j = if i = j then -1 else 1 := rfl

/-- `R` is symmetric. -/
theorem reggeMatrix_transpose : reggeMatrix.transpose = reggeMatrix := by
  ext i j
  by_cases h : i = j
  · subst j
    simp
  · simp [Matrix.transpose_apply, reggeMatrix, h, Ne.symm h]

/-- Coordinate formula for the Regge action. -/
theorem reggeMatrix_mulVec_apply (v : Four → ℚ) (i : Four) :
    reggeMatrix.mulVec v i = (1 / 2 : ℚ) * (∑ j, v j) - v i := by
  classical
  rw [Matrix.mulVec, dotProduct]
  simp only [reggeMatrix_apply, sub_mul, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  simp

/-- Every column of `R` has sum one. -/
theorem reggeMatrix_column_sum (j : Four) : ∑ i, reggeMatrix i j = 1 := by
  classical
  simp [reggeMatrix]
  norm_num

/-- The manuscript's identity `R² = I₄`. -/
theorem reggeMatrix_mul_self : reggeMatrix * reggeMatrix = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  change reggeMatrix.mulVec (fun k => reggeMatrix k j) i = (1 : Matrix Four Four ℚ) i j
  rw [reggeMatrix_mulVec_apply, reggeMatrix_column_sum]
  by_cases h : i = j
  · subst j
    simp [reggeMatrix]
  · simp [reggeMatrix, h]

/-- Symmetry and involutivity imply orthogonality. -/
theorem reggeMatrix_orthogonal :
    reggeMatrix.transpose * reggeMatrix = 1 := by
  rw [reggeMatrix_transpose, reggeMatrix_mul_self]

/-- The sign matrix really is twice the Regge matrix. -/
theorem hadamardMatrix_eq_two_smul :
    hadamardMatrix = (2 : ℚ) • reggeMatrix := by
  ext i j
  by_cases h : i = j
  · simp [hadamardMatrix, reggeMatrix, h]
    norm_num
  · simp [hadamardMatrix, reggeMatrix, h]

/-- The identity `Hᵗ H = 4 I₄` used in the four-channel cancellation. -/
theorem hadamardMatrix_orthogonal :
    hadamardMatrix.transpose * hadamardMatrix = (4 : ℚ) • (1 : Matrix Four Four ℚ) := by
  ext i j
  have h := congr_fun (congr_fun reggeMatrix_orthogonal i) j
  rw [hadamardMatrix_eq_two_smul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] at h ⊢
  calc
    ∑ x, (2 * reggeMatrix x i) * (2 * reggeMatrix x j) =
        4 * ∑ x, reggeMatrix x i * reggeMatrix x j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = 4 * (1 : Matrix Four Four ℚ) i j := by rw [h]

/-- `R` fixes the constant line. -/
theorem reggeMatrix_mulVec_const (c : ℚ) :
    reggeMatrix.mulVec (fun _ => c) = fun _ => c := by
  ext i
  rw [reggeMatrix_mulVec_apply]
  simp
  ring

/-- `R` is minus the identity on the hyperplane whose coordinates sum to zero. -/
theorem reggeMatrix_mulVec_of_sum_eq_zero (v : Four → ℚ)
    (hv : ∑ j, v j = 0) :
    reggeMatrix.mulVec v = fun i => -v i := by
  ext i
  rw [reggeMatrix_mulVec_apply, hv]
  ring

/-- Applying the Regge linear action twice returns the original vector. -/
theorem reggeMatrix_mulVec_involutive (v : Four → ℚ) :
    reggeMatrix.mulVec (reggeMatrix.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, reggeMatrix_mul_self]
  simp

end SphericalReggeScissors
