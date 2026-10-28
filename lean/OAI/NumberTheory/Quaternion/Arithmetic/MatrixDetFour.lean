import Mathlib

/-! # Matrix Det Four -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.MatrixDetFour

noncomputable section

/-! An explicit four-by-four determinant expansion, with each
three-by-three minor reindexed separately. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {R : Type*} [CommRing R]

theorem matrix_det_four_expand (M : Matrix (Fin 4) (Fin 4) R) :
    M.det =
      M 0 0 * (!![M 1 1, M 1 2, M 1 3; M 2 1, M 2 2, M 2 3; M 3 1, M 3 2, M 3 3]).det -
      M 0 1 * (!![M 1 0, M 1 2, M 1 3; M 2 0, M 2 2, M 2 3; M 3 0, M 3 2, M 3 3]).det +
      M 0 2 * (!![M 1 0, M 1 1, M 1 3; M 2 0, M 2 1, M 2 3; M 3 0, M 3 1, M 3 3]).det -
      M 0 3 * (!![M 1 0, M 1 1, M 1 2; M 2 0, M 2 1, M 2 2; M 3 0, M 3 1, M 3 2]).det := by
  have h0 : M.submatrix Fin.succ (0 : Fin 4).succAbove =
      !![M 1 1, M 1 2, M 1 3; M 2 1, M 2 2, M 2 3; M 3 1, M 3 2, M 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h1 : M.submatrix Fin.succ (1 : Fin 4).succAbove =
      !![M 1 0, M 1 2, M 1 3; M 2 0, M 2 2, M 2 3; M 3 0, M 3 2, M 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h2 : M.submatrix Fin.succ (2 : Fin 4).succAbove =
      !![M 1 0, M 1 1, M 1 3; M 2 0, M 2 1, M 2 3; M 3 0, M 3 1, M 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h3 : M.submatrix Fin.succ (3 : Fin 4).succAbove =
      !![M 1 0, M 1 1, M 1 2; M 2 0, M 2 1, M 2 2; M 3 0, M 3 1, M 3 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four, h0, h1, h2, h3]
  norm_num
  ring

end

end OAI.NumberTheory.Quaternion.Arithmetic.MatrixDetFour
