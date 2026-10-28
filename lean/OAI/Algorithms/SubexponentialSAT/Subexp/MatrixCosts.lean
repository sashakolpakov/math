import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

namespace OAI.Algorithms

/-! Numeric budgets for the actual scalar, row, and two-product traces. -/

namespace SubexponentialSAT.Subexp.MatrixProgram

def termBudget (B : ℕ) : ℕ := 12000 * (B + 1) ^ 2 + 30 * B + 26

end SubexponentialSAT.Subexp.MatrixProgram

namespace SubexponentialSAT.Subexp.MatrixVectorProgram

def rowBudget (N B : ℕ) : ℕ :=
  N * (MatrixProgram.termBudget B + 2) + 7 * (N * (2 * B + 1)) + 21 * B + 27

def matrixBudget (m N B : ℕ) : ℕ := m * (rowBudget N B + 6 * B + 5) + 6

end SubexponentialSAT.Subexp.MatrixVectorProgram

namespace SubexponentialSAT.Subexp.MatrixPairProgram

def budget (m N B : ℕ) : ℕ :=
  MatrixVectorProgram.matrixBudget N N B + MatrixVectorProgram.matrixBudget m N B +
    15 * (N * (2 * B + 1)) + 7 * (m * (N * (2 * B + 1))) + 7 * m + 25

theorem callback_bound (m N B d : ℕ) (hd : d ≤ N) :
    budget m N B + 3 * (N * (2 * B + 1)) + 7 * (N * (N * (2 * B + 1))) + 7 * N +
      (12 * (N * (2 * B + 1)) + 23 * (N * (2 * B + 1)) +
        12 * (m * (2 * B + 1)) + 7 * d + 65) + 13 ≤
      200000 * (m + 1) * (N + 1) ^ 2 * (B + 1) ^ 2 := by
  unfold budget MatrixVectorProgram.matrixBudget MatrixVectorProgram.rowBudget MatrixProgram.termBudget
  ring_nf
  omega

end SubexponentialSAT.Subexp.MatrixPairProgram

end OAI.Algorithms
