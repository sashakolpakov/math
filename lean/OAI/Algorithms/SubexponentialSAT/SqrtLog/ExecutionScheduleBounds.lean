import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionScheduleLocal

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Execution.ScheduleLocal

/-- A coarse uniform cubic envelope, including clearing the old schedule. -/
theorem bound_cubic (N O : ℕ) :
    bound N O ≤ 40000000000000 * (N+O+1)^3 := by
  let X := N+O+1
  have hx : 1 ≤ X := by dsimp [X]; omega
  have h1 : N+1 ≤ X := by dsimp [X]; omega
  have h2 : (N+5)+(N+18)+(N+17)+2 ≤ 42*X := by dsimp [X]; omega
  have h3 : (N+5)+(N+18)+(N+17)+O+1 ≤ 41*X := by dsimp [X]; omega
  have hp2 := Nat.pow_le_pow_left h1 2
  have hp3 := Nat.pow_le_pow_left h2 3
  have hx2 : X^2 ≤ X^3 := by
    calc
      X^2 = X^2*1 := by simp
      _ ≤ X^2*X := Nat.mul_le_mul_left _ hx
      _ = X^3 := by ring
  have hx3 : X ≤ X^3 := by
    have h : X ≤ X^2 := by nlinarith
    exact h.trans hx2
  dsimp [bound]
  change _ ≤ 40000000000000*X^3
  nlinarith

end SubexponentialSAT.SqrtLog.Execution.ScheduleLocal

end OAI.Algorithms
