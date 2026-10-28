import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgramCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram

namespace OAI.Algorithms

/-! Polynomial bit bounds for the fixed source interpreter. Source size and
raw literal bytes are charged separately from the retained coefficient count. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

def addCost (B d J : ℕ) : ℕ :=
  binaryBound (DensePolynomialProgram.AddService.budget d B J J) (J*(d*B))
def mulCost (B d J : ℕ) : ℕ :=
  binaryBound (DensePolynomialProgram.nativeMulBudget J d B) (J*(d*B))


def totalBudget {B d : ℕ} (J : ℕ) (e : SubexponentialSAT.Algorithm.Expr (List (Coeff B d))) : ℕ :=
  300000*(e.size + literalBytes e + 1)*(J+1)^3*(d+1)^3*(B+1)^2

theorem totalBudget_le_source {B d : ℕ} (J : ℕ)
    (e : SubexponentialSAT.Algorithm.Expr (List (Coeff B d))) :
    totalBudget J e ≤
      300000 * ((SubexponentialSAT.SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile).length+1) *
        (J+1)^3 * (d+1)^3 * (B+1)^2 := by
  have h : e.size + literalBytes e + 1 ≤
      (SubexponentialSAT.SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile).length + 1 := by
    rw [source_length]
    omega
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)))

theorem callbackCost_polynomial (B d J : ℕ) :
    addCost B d J + mulCost B d J + 16*(J*(d*B)) + 100 ≤
      300000*(J+1)^3*(d+1)^3*(B+1)^2 := by
  have hm := DensePolynomialProgram.nativeMulBudget_polynomial J d B
  unfold addCost mulCost binaryBound DensePolynomialProgram.AddService.budget
  ring_nf at *
  omega

theorem executionCost_native_polynomial {B d : ℕ} (J : ℕ)
    (e : SubexponentialSAT.Algorithm.Expr (List (Coeff B d))) :
    executionCost (addCost B d J) (mulCost B d J) (J*(d*B)) e + 5 ≤ totalBudget J e := by
  have h := (executionCost_polynomial (addCost B d J) (mulCost B d J) (J*(d*B)) e).trans
    (Nat.mul_le_mul_left _ (callbackCost_polynomial B d J))
  let A := e.size + literalBytes e
  let C := 300000*(J+1)^3*(d+1)^3*(B+1)^2
  change executionCost (addCost B d J) (mulCost B d J) (J*(d*B)) e ≤ A*C at h
  have hC : 5 ≤ C := by
    let P := (J+1)^3*(d+1)^3*(B+1)^2
    have hP : 0 < P := by dsimp [P]; positivity
    have he : C = 300000*P := by dsimp [C,P]; ring
    rw [he]
    omega
  calc
    executionCost (addCost B d J) (mulCost B d J) (J*(d*B)) e + 5 ≤ A*C+C :=
      Nat.add_le_add h hC
    _ = (A+1)*C := by simpa only [Nat.one_mul] using (Nat.add_mul A 1 C).symm
    _ = totalBudget J e := by dsimp [A,C,totalBudget]; ring


end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
