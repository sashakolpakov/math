import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramWord

namespace OAI.Algorithms

/-! Uniform bit lengths for every matrix and word, including rejected
candidates. These bounds do not depend on matrix entries or search success. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.Subexp

theorem framedCellStream_length (cells : List (Bool × Bool)) :
    (framedCellStream cells).length = 5 * cells.length := by
  induction cells with
  | nil => rfl
  | cons x xs ih => simp [framedCellStream, ih]; omega

theorem scalarFrames_ternary_length (xs : List SparseCode.F3) :
    (scalarFrames xs).length = 5 * xs.length := by
  rw [scalarFrames_ternary, framedCellStream_length, List.length_map]

theorem matrixFrames_ternary_length {t D : ℕ}
    (Q : Fin t → Fin D → SparseCode.F3) : (matrixFrames Q).length = 5 * (t * D) := by
  rw [← framedMatrix_eq_matrixFrames, framedMatrix, framedVector_eq_scalarFrames,
    scalarFrames_ternary_length, List.length_ofFn]

theorem modulus_three : MatrixWordEncoding.modulus 3 = [true,true,false] := by
  norm_num [MatrixWordEncoding.modulus, MatrixWordEncoding.width,
    SubexpLiftRing.baseWidth, SubexpLiftRing.fixedBits]

theorem zero_three : MatrixWordEncoding.zero 3 = [false,false] := by
  norm_num [MatrixWordEncoding.zero, MatrixWordEncoding.word, MatrixWordEncoding.width,
    SubexpLiftRing.baseWidth, SubexpLiftRing.fixedBits]

def wordInputSpan (t D d : ℕ) := 5 * (t * D) + 5 * D + t + d + 5

theorem wordInput_length_le {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ) (regs : Fin 8 → Bool) (i : Fin 18) :
    ((extendMatrixState (matrixInput Q x regs) d []).stacks i).length ≤
      wordInputSpan t D d := by
  have hm := matrixFrames_ternary_length Q
  have hx := scalarFrames_ternary_length (List.ofFn x)
  simp only [List.length_ofFn] at hx
  have h16 : (16 : Fin 18).val = 16 := rfl
  fin_cases i <;>
    norm_num [extendMatrixState, matrixInput, MatrixScalarProgram.state, MatrixScalarProgram.scalarStacks,
      modulus_three, zero_three, wordInputSpan, hm, hx, Fin.ext_iff, h16] <;> omega

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
