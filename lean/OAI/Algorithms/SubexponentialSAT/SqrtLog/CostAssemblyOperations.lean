import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyMoment

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly

/-- Ring/key operations for all supports: stored moments, support weights,
per-head local-jet preparation, output extraction, and explicit mask storage.
`prep` is a cost per bucket assignment and support. -/
def queryArithmetic (M N H n t J prep : ℕ) : ℕ :=
  momentWork M N H t J + M*N*J + M*N*prep +
    J*t*(t*J*M+1) + (2*n+2)*M+1

/-- The only exponential resources are support count M and bucket enumeration
E. All other dimensions are bounded by the explicit ordinary parameter S. -/
theorem queryArithmetic_le (M N H n t J prep S E : ℕ)
    (hS : 1 ≤ S) (hE : N+H+1 ≤ E) (hn : n+1 ≤ S)
    (ht : t+1 ≤ S) (hJ : J+1 ≤ S) (hp : prep+1 ≤ S) :
    queryArithmetic M N H n t J prep ≤ 14*E*S^8*(M+1)^4 := by
  have hE1 : 1 ≤ E := by omega
  have hN : N ≤ E := by omega
  have hS2 : S ≤ S^2 := by nlinarith
  have hS4 : S^2 ≤ S^4 := by simpa [← pow_mul] using Nat.pow_le_pow_left hS2 2
  have hS8 : S^4 ≤ S^8 := by simpa [← pow_mul] using Nat.pow_le_pow_left hS4 2
  have h18 : 1 ≤ S^8 := hS.trans (hS2.trans (hS4.trans hS8))
  have hM1 : 1 ≤ M+1 := by omega
  have hM2 : M+1 ≤ (M+1)^2 := by nlinarith
  have hM4 : (M+1)^2 ≤ (M+1)^4 := by simpa [← pow_mul] using Nat.pow_le_pow_left hM2 2
  have hM14 : M+1 ≤ (M+1)^4 := hM2.trans hM4
  have hS6 : S^6 ≤ S^8 := by
    calc
      S^6 = S^2*S^4 := by ring
      _ ≤ S^4*S^4 := Nat.mul_le_mul_right _ hS4
      _ = S^8 := by ring
  let Z := E*S^8*(M+1)^4
  have hmoment : momentWork M N H t J ≤ 7*Z := by
    calc
      _ ≤ 7*(N+H+1)*(t+1)^3*(J+1)^3*(M+1)^4 := momentWork_le ..
      _ ≤ 7*E*S^3*S^3*(M+1)^4 := by gcongr
      _ = 7*E*S^6*(M+1)^4 := by ring
      _ ≤ 7*E*S^8*(M+1)^4 := by gcongr
      _ = 7*Z := by dsimp [Z]; ring
  have hweight : M*N*J ≤ Z := by
    calc
      M*N*J ≤ (M+1)^4*E*S^8 := by gcongr <;> omega
      _ = Z := by dsimp [Z]; ring
  have hprep : M*N*prep ≤ Z := by
    calc
      M*N*prep ≤ (M+1)^4*E*S^8 := by gcongr <;> omega
      _ = Z := by dsimp [Z]; ring
  have hread : J*t*(t*J*M+1) ≤ 2*Z := by
    have hi : t*J*M+1 ≤ 2*S^2*(M+1) := by
      have hh : t*J*M ≤ S*S*(M+1) := by gcongr <;> omega
      nlinarith [Nat.mul_le_mul hS2 hM1]
    calc
      _ ≤ S*S*(2*S^2*(M+1)) := by gcongr <;> omega
      _ = 2*S^4*(M+1) := by ring
      _ ≤ 2*E*S^8*(M+1)^4 := by
        calc
          _ ≤ 2*1*S^8*(M+1)^4 := by gcongr
          _ ≤ _ := by gcongr
      _ = 2*Z := by dsimp [Z]; ring
  have hstore : (2*n+2)*M+1 ≤ 3*Z := by
    have hz : S*(M+1) ≤ Z := by
      calc
        _ ≤ 1*S^8*(M+1)^4 := by gcongr; omega
        _ ≤ Z := by dsimp [Z]; gcongr
    have hz1 : 1 ≤ Z := by
      calc
        1 ≤ S*(M+1) := one_le_mul_of_one_le_of_one_le hS hM1
        _ ≤ Z := hz
    have hh : (2*n+2)*M ≤ 2*S*(M+1) := by gcongr <;> omega
    nlinarith
  calc
    _ ≤ 7*Z+Z+Z+2*Z+3*Z := by unfold queryArithmetic; omega
    _ = _ := by dsimp [Z]; ring

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
