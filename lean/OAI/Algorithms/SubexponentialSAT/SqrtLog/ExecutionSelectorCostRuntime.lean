import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionSelectorCostNumeric
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionFinalCostAlgebra

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Execution.SelectorCost
open Statement FinalCost

/-- Fixed polynomial envelopes for the source and selector bookkeeping compose
with the actual rounded query budget. No query time is raised to a power. -/
theorem envelope_runtime {Ch Ah Cs As Cq Aq : ℝ}
    (_hCh : 0 ≤ Ch) (_hCs : 0 ≤ Cs) (hCq : 1 ≤ Cq) (hAq : 0 ≤ Aq)
    (dh ds dq W n H source Q cost : ℕ)
    (hH : (H:ℝ)+1 ≤ runtimeBound Ch Ah dh W n)
    (hsource : (source:ℝ)+1 ≤ runtimeBound Cs As ds W n)
    (hQ : Q ≤ Nat.ceil (runtimeBound Cq Aq dq source n))
    (hcost : cost ≤ 1000000*(H+1)^8*(Q+1)) :
    (cost:ℝ) ≤ runtimeBound (3000000*Ch^8*(Cq*Cs^dq))
      ((8:ℝ)*Ah+(Aq+(dq:ℝ)*As)) (dh*8+ds*dq) W n := by
  have hqp : (Q:ℝ)+1 ≤ 3*runtimeBound Cq Aq dq source n := by
    have hceil := Execution.ceil_runtimeBound_le hCq hAq dq source n
    have hone := one_le_runtimeBound hCq hAq dq source n
    have hh : (Q:ℝ) ≤ (Nat.ceil (runtimeBound Cq Aq dq source n):ℝ) := by exact_mod_cast hQ
    linarith
  have hs := runtimeBound_substitute (C:=Cq) (A:=Aq) (H:=Cs) (B:=As)
    (by linarith) dq ds W source n hsource
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (H:ℝ)+1) hH 8
  have hb : (cost:ℝ) ≤ 1000000*((H:ℝ)+1)^8*((Q:ℝ)+1) := by exact_mod_cast hcost
  calc
    _ ≤ 1000000*(runtimeBound Ch Ah dh W n)^8*
        (3*runtimeBound (Cq*Cs^dq) (Aq+(dq:ℝ)*As) (ds*dq) W n) := by
      apply hb.trans
      gcongr
      exact hqp.trans (mul_le_mul_of_nonneg_left hs (by norm_num))
    _ = runtimeBound (3000000*Ch^8) ((8:ℝ)*Ah) (dh*8) W n *
        runtimeBound (Cq*Cs^dq) (Aq+(dq:ℝ)*As) (ds*dq) W n := by
      rw [runtimeBound_pow]
      unfold runtimeBound
      ring_nf
    _ = _ := by rw [runtimeBound_product]

end SubexponentialSAT.SqrtLog.Execution.SelectorCost

end OAI.Algorithms
