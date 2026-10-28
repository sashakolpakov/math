import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsStored

namespace OAI.Algorithms

/-! A concrete polynomial envelope for the stored sparse moment algorithm.
These are algebra/key-scan costs; primitive bit overhead is an additional
multiplicative resource supplied by the machine refinement. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

/-- The exact right hand side of `Moments.Stored.run_cost`, for all M supports. -/
def momentWork (M N H t J : ℕ) : ℕ :=
  let L := t * J * M
  M * (N * (L + 2 * L * (2 * L + 1)) +
    H * (L^2 * (2 * L + 2)) + L * (2 * L + 2) + 2 * L * (2 * L + 1))

/-- Four powers of M suffice; no enumeration of global assignment tuples
is hidden in this bound. N counts the sum of the head bucket sizes. -/
theorem momentWork_le (M N H t J : ℕ) :
    momentWork M N H t J ≤
      7 * (N + H + 1) * (t + 1)^3 * (J + 1)^3 * (M + 1)^4 := by
  let L := t * J * M
  have h1 : L + 2 * L * (2 * L + 1) ≤ 7 * (L + 1)^2 := by nlinarith
  have h2 : L^2 * (2 * L + 2) ≤ 2 * (L + 1)^3 := by nlinarith
  have h3 : L * (2 * L + 2) + 2 * L * (2 * L + 1) ≤ 6 * (L + 1)^2 := by nlinarith
  have hpow : (L+1)^2 ≤ (L+1)^3 := by nlinarith
  have hsum : N * (L + 2 * L * (2 * L + 1)) +
      H * (L^2 * (2 * L + 2)) + L * (2 * L + 2) + 2 * L * (2 * L + 1) ≤
      7 * (N + H + 1) * (L + 1)^3 := by
    have hN := Nat.mul_le_mul_left N h1
    have hH := Nat.mul_le_mul_left H h2
    have hNp := Nat.mul_le_mul_left (7*N) hpow
    have h6p := Nat.mul_le_mul_left 6 hpow
    nlinarith
  have hL : L + 1 ≤ (t+1)*(J+1)*(M+1) := by dsimp [L]; nlinarith
  have hc := Nat.pow_le_pow_left hL 3
  calc
    momentWork M N H t J ≤ M * (7 * (N+H+1)*(L+1)^3) :=
      Nat.mul_le_mul_left M hsum
    _ ≤ (M+1) * (7 * (N+H+1)*((t+1)*(J+1)*(M+1))^3) := by gcongr; omega
    _ = _ := by ring

/-- A single explicit dimension parameter can dominate every ordinary
polynomial resource, while M is kept separate to preserve entropy. -/
theorem momentWork_le_dimension (M N H t J S : ℕ)
    (hN : N + H + 1 ≤ S) (ht : t + 1 ≤ S) (hJ : J + 1 ≤ S) :
    momentWork M N H t J ≤ 7 * S^7 * (M+1)^4 := by
  calc
    momentWork M N H t J ≤ 7*(N+H+1)*(t+1)^3*(J+1)^3*(M+1)^4 := momentWork_le ..
    _ ≤ 7*S*S^3*S^3*(M+1)^4 := by gcongr
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
