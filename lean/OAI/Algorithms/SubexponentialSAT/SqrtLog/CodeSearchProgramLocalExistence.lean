import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramMatrixScan

namespace OAI.Algorithms

/-! The finite local-code existence theorem discharges search success. It is
used only to prove that the fixed exhaustive machine finds a matrix; it is
not an instruction, an input, or a candidate-selection oracle. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram

theorem local_matrix_search_runsIn (D B ell t : ℕ)
    (hB : 0 < B) (hell : 0 < ell) (hD : D ≤ 2 ^ ell) (ht : D ≤ 8 * B * t)
    (base : MatrixSearchState)
    (hb : MatrixInvariant t D (D / (100 * B * ell) + 1) base) (v pr f : Bool) :
    ∃ (out : MatrixSearchState) (tail : List Bool)
      (Q : Fin t → Fin D → SparseCode.F3),
      SparseCode.HasDistance Q (D / (100 * B * ell) + 1) ∧
      out.stacks 18 = matrixFrames Q ∧
      RunsIn matrixSearchProgram (matrixSearchBudget t D (D / (100 * B * ell) + 1))
        ((RecordPrograms.state matrixPorts base v pr f
          (ProgramEncoding.encodeRecords (framedCandidates 3 (t * D))) []).withPC
            (some matrixSearchProgram.entry))
        ((RecordPrograms.state matrixPorts out false true true tail []).withPC none) := by
  exact matrix_search_runsIn base hb
    ⟨LocalCode.localMatrix D B ell t,LocalCode.localMatrix_distance D B ell t hB hell hD ht⟩
    v pr f

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
