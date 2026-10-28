import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticLayoutCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectTermination

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic

/-- Sparse clauses have only logarithmic binary length. The upper bound here
is intentionally elementary; it is enough for the linear precision budget. -/
theorem sparse_clause_size_le (n m B q : ℕ) (hm : m ≤ n*B) (hB : B ≤ L n^q) :
    Nat.size m ≤ (q+1)*L n+1 := by
  have hn : n ≤ 2^L n := by
    have hh : n+16 < 2^L n := by simpa [L] using (Nat.lt_log2_self (n:=n+16))
    omega
  have hL : L n ≤ 2^L n := (Nat.lt_two_pow_self).le
  have hpow : m ≤ 2^((q+1)*L n) := by
    calc
      m ≤ n*B := hm
      _ ≤ 2^L n*(2^L n)^q := Nat.mul_le_mul hn (hB.trans (Nat.pow_le_pow_left hL q))
      _ = 2^((q+1)*L n) := by rw [← pow_mul, ← pow_add]; congr 1; ring
  apply Nat.size_le.mpr
  exact hpow.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

theorem eventually_sparse_clause_size (m B : ℕ → ℕ) (q : ℕ)
    (hm : ∀ᶠ n:ℕ in atTop, m n ≤ n*B n)
    (hB : ∀ᶠ n:ℕ in atTop, B n ≤ L n^q) :
    ∀ᶠ n:ℕ in atTop, Nat.size (m n) ≤ n := by
  have hb := eventually_L_power_le_n 1 (show (0:ℝ) < (q:ℝ)+2 by positivity)
  filter_upwards [hm,hB,hb] with n hmn hBn hbn
  have hh := sparse_clause_size_le n (m n) (B n) q hmn hBn
  have hLn : 1 ≤ L n := L_pos n
  have hbn' : (q+2)*L n ≤ n := by exact_mod_cast (by simpa using hbn : ((q:ℝ)+2)*(L n:ℝ) ≤ n)
  nlinarith

/-- This includes a trial row and a marked clause. With the actual loop cap,
a conservative fixed coefficient 30 bounds the jet's precision/factor term. -/
theorem linear_jet_envelope (n m factors : ℕ) (hn : 1 ≤ n)
    (hm : Nat.size m ≤ n) (hf : factors ≤ 3*n+HashSelect.loopCap n m+1) :
    2*factors+3*(LeafParametersProgram.precision n m-1)+1 ≤ 30*n := by
  unfold HashSelect.loopCap at hf
  unfold LeafParametersProgram.precision
  omega

theorem eventually_linear_jet_envelope (m B factors : ℕ → ℕ) (q : ℕ)
    (hm : ∀ᶠ n:ℕ in atTop, m n ≤ n*B n)
    (hB : ∀ᶠ n:ℕ in atTop, B n ≤ L n^q)
    (hf : ∀ᶠ n:ℕ in atTop, factors n ≤ 3*n+HashSelect.loopCap n (m n)+1) :
    ∀ᶠ n:ℕ in atTop,
      2*factors n+3*(LeafParametersProgram.precision n (m n)-1)+1 ≤ 30*n := by
  filter_upwards [eventually_sparse_clause_size m B q hm hB,hf,eventually_ge_atTop 1]
    with n hmn hfn hn
  exact linear_jet_envelope n (m n) (factors n) hn hmn hfn

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
