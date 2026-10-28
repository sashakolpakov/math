import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblySearch
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeParameters
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBounds

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic

theorem code_logSize_le (n m B q : ℕ) (hm : m ≤ n*B) (hB : B ≤ L n^q) :
    SparseCode.logSize m ≤ (q+2)*L n := by
  have hL : 1 ≤ L n := L_pos n
  by_cases hz : m=0
  · subst m
    simp only [SparseCode.logSize, Nat.log_zero_right, zero_add]
    nlinarith
  have hs := sparse_clause_size_le n m B q hm hB
  have he : SparseCode.logSize m=Nat.size m := by
    rw [LeafParametersProgram.size_eq_log2_add_one hz]
    simp [SparseCode.logSize, Nat.log2_eq_log_two]
  rw [he]
  nlinarith

theorem code_distanceDenom_le (n m B q : ℕ) (hm : m ≤ n*B) (hB : B ≤ L n^q) :
    SparseCode.distanceDenom m B ≤ 20000*(q+2)^2*L n^(2*q+2) := by
  have hl := code_logSize_le n m B q hm hB
  unfold SparseCode.distanceDenom
  calc
    _ ≤ 20000*(L n^q)^2*((q+2)*L n)^2 := by gcongr
    _ = _ := by ring

theorem code_degreeBound_le (n m B q : ℕ) (hm : m ≤ n*B) (hB : B ≤ L n^q) :
    SparseCode.degreeBound m B ≤ 320000*(q+2)^3*L n^(2*q+3) := by
  have hl := code_logSize_le n m B q hm hB
  unfold SparseCode.degreeBound SparseCode.gapDenom
  calc
    _ ≤ 8*(200*(L n^q)*((q+2)*L n))^2*((q+2)*L n) := by gcongr
    _ = _ := by ring

theorem eventually_code_distanceDenom (m B : ℕ → ℕ) (q : ℕ)
    (hm : ∀ᶠ n:ℕ in atTop, m n ≤ n*B n)
    (hB : ∀ᶠ n:ℕ in atTop, B n ≤ L n^q) :
    ∀ᶠ n:ℕ in atTop, SparseCode.distanceDenom (m n) (B n) ≤ L n^(2*q+3) := by
  apply eventually_absorb_L_coefficient
    (fun n => SparseCode.distanceDenom (m n) (B n)) (20000*(q+2)^2) (2*q+2)
  filter_upwards [hm,hB] with n hn hbn
  exact code_distanceDenom_le n (m n) (B n) q hn hbn

/-- The exact all-candidate/all-marked-clause query count from HashSelect,
with its actual sparse-code exponent, fits a single target exponential. -/
theorem eventually_constructed_hashCalls (m B : ℕ → ℕ) (q : ℕ)
    (hm : ∀ᶠ n:ℕ in atTop, m n ≤ n*B n)
    (hB : ∀ᶠ n:ℕ in atTop, B n ≤ L n^q) :
    ∀ᶠ n:ℕ in atTop,
      (hashCalls n (m n) (SparseCode.distanceDenom (m n) (B n)):ℝ) ≤
        (2:ℝ)^Statement.runtimeScale n :=
  eventually_hashCalls_target m B (fun n => SparseCode.distanceDenom (m n) (B n))
    q (2*q+3) hm hB (eventually_code_distanceDenom m B q hm hB)

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
