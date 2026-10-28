import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyOperations
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyEnumeration

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly

/-- Summed head buckets, including one unit of loop overhead, are bounded by
three copies of the full head-enumeration counter. -/
theorem bucket_dimension_le (N H heads headSize : ℕ) (hh : 1 ≤ heads)
    (hN : N ≤ heads*2^headSize) (hH : H ≤ heads) :
    N+H+1 ≤ 3*(heads*2^headSize) := by
  have hp : 1 ≤ 2^headSize := Nat.one_le_pow _ _ (by decide)
  have hb : heads ≤ heads*2^headSize := by nlinarith
  omega

/-- The large number of bucket assignments stays in enumerationWork. The
ordinary parameter 42*S contains only dimensions and per-assignment costs. -/
theorem labelled_queryArithmetic_le
    (M N H n t J prep S base rows heads headSize : ℕ)
    (hS : 1 ≤ S) (hh : 1 ≤ heads) (hN : N ≤ heads*2^headSize) (hH : H ≤ heads)
    (hn : n+1 ≤ S) (ht : t+1 ≤ S) (hJ : J+1 ≤ S) (hp : prep+1 ≤ S) :
    base^rows * queryArithmetic M N H n t J prep ≤
      enumerationWork base rows heads headSize * (42*S+1)^8 * (M+1)^4 := by
  have hq := queryArithmetic_le M N H n t J prep S (3*(heads*2^headSize)) hS
    (bucket_dimension_le N H heads headSize hh hN hH) hn ht hJ hp
  have hscale : 42*S^8 ≤ (42*S+1)^8 := by
    calc
      42*S^8 ≤ 42^8*S^8 := by gcongr; norm_num
      _ = (42*S)^8 := by rw [mul_pow]
      _ ≤ _ := by gcongr; omega
  calc
    _ ≤ base^rows*(14*(3*(heads*2^headSize))*S^8*(M+1)^4) :=
      Nat.mul_le_mul_left _ hq
    _ = enumerationWork base rows heads headSize*(42*S^8)*(M+1)^4 := by
      unfold enumerationWork
      ring
    _ ≤ _ := by gcongr

/-- The separate pruned support generator is still polynomial times M. Its
cost can share the same fourth-power support envelope. -/
theorem support_generator_envelope (n J M S : ℕ) (hn : n+1 ≤ S) (hJ : J+1 ≤ S) :
    4000*(n+1)*(n+J+1)*M ≤ 8000*S^2*(M+1)^4 := by
  have hsum : n+J+1 ≤ 2*S := by omega
  have hm : M ≤ (M+1)^4 := (Nat.le_succ M).trans (Nat.le_self_pow (by decide) _)
  calc
    _ ≤ 4000*S*(2*S)*(M+1)^4 := by gcongr
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
