import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyParameters

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic

/-- A variable exponent polynomial in log n still gives negligible search
cost, even with an alphabet polynomial in n. -/
theorem eventually_polylog_degree_target (d : ℕ → ℕ) (q : ℕ) {C : ℝ}
    (hC : 0 < C) (hd : ∀ᶠ n:ℕ in atTop, (d n:ℝ) ≤ C*(L n:ℝ)^q) :
    ∀ᶠ n:ℕ in atTop, (((n+1)^d n:ℕ):ℝ) ≤ (2:ℝ)^Statement.runtimeScale n := by
  have hp := eventually_polylog_le_target (q+1)
    (show (0:ℝ) < C*2^q by positivity)
  filter_upwards [hd,hp] with n hdn hpn
  have hlog : Real.logb 2 ((n:ℝ)+1) ≤ logSize n :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.logb 2 ((n:ℝ)+1) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
  have he : (d n:ℝ)*Real.logb 2 ((n:ℝ)+1) ≤ Statement.runtimeScale n := by
    calc
      _ ≤ (C*(2*logSize n)^q)*logSize n := by
        apply mul_le_mul
        · exact hdn.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (L_le_twice_logSize n) q) hC.le)
        · exact hlog
        · exact hlog0
        · have := four_le_logSize n
          positivity
      _ = (C*2^q)*logSize n^(q+1) := by rw [mul_pow, pow_succ]; ring
      _ ≤ _ := hpn
  have heq : (((n+1)^d n:ℕ):ℝ)=(2:ℝ)^((d n:ℝ)*Real.logb 2 ((n:ℝ)+1)) := by
    push_cast
    rw [← Real.rpow_natCast]
    exact SubexpExponentArithmetic.rpow_eq_two_rpow_logb (by positivity) _
  rw [heq]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) he

/-- All failed candidates and all marked-clause counts, plus the final count. -/
def hashCalls (n m P : ℕ) : ℕ :=
  2*(3*m)^P*HashSelect.loopCap n m*m+1

theorem hashCalls_le (n m P : ℕ) (hn : 1 ≤ n) (hm : m ≤ n^2)
    (hsize : Nat.size m ≤ n) :
    hashCalls n m P ≤ (n+1)^(3*P+7) := by
  have hsq : n ≤ n^2 := by nlinarith
  have hbase : 3*m ≤ (n+1)^3 := by nlinarith
  have hcap : HashSelect.loopCap n m ≤ (n+1)^3 := by
    unfold HashSelect.loopCap
    nlinarith
  have hm' : m ≤ (n+1)^2 := by nlinarith
  have hprod : 2*(3*m)^P*HashSelect.loopCap n m*m ≤ (n+1)^(3*P+6) := by
    calc
      _ ≤ (n+1)*((n+1)^3)^P*(n+1)^3*(n+1)^2 := by gcongr; omega
      _ = _ := by rw [← pow_mul]; ring
  have hpos : 1 ≤ (n+1)^(3*P+6) := Nat.one_le_pow _ _ (by omega)
  unfold hashCalls
  calc
    _ ≤ 2*(n+1)^(3*P+6) := by omega
    _ ≤ (n+1)*(n+1)^(3*P+6) := by gcongr; omega
    _ = _ := by rw [← pow_succ']

theorem eventually_hashCalls_target (m B P : ℕ → ℕ) (q v : ℕ)
    (hm : ∀ᶠ n:ℕ in atTop, m n ≤ n*B n)
    (hB : ∀ᶠ n:ℕ in atTop, B n ≤ L n^q)
    (hP : ∀ᶠ n:ℕ in atTop, P n ≤ L n^v) :
    ∀ᶠ n:ℕ in atTop, (hashCalls n (m n) (P n):ℝ) ≤
      (2:ℝ)^Statement.runtimeScale n := by
  have hdeg : ∀ᶠ n:ℕ in atTop, ((3*P n+7:ℕ):ℝ) ≤ 10*(L n:ℝ)^v := by
    filter_upwards [hP] with n hn
    have hp : 1 ≤ L n^v := Nat.one_le_pow _ _ (L_pos n)
    have : 3*P n+7 ≤ 10*L n^v := by omega
    exact_mod_cast this
  have hpow := eventually_polylog_degree_target (fun n => 3*P n+7) v
    (by norm_num : (0:ℝ) < 10) hdeg
  have hBn := eventually_L_power_le_n q (by norm_num : (0:ℝ) < 1)
  filter_upwards [hm,hB,hBn,eventually_sparse_clause_size m B q hm hB,
    hpow,eventually_ge_atTop 1] with n hmn hbn hnB hnsize hnPow hn
  have hbnum : B n ≤ n := by
    have hh : L n^q ≤ n := by exact_mod_cast (by simpa using hnB : (L n:ℝ)^q ≤ n)
    exact hbn.trans hh
  have hm2 : m n ≤ n^2 := by nlinarith
  exact (show (hashCalls n (m n) (P n):ℝ) ≤ ((n+1)^(3*P n+7):ℕ) by
    exact_mod_cast hashCalls_le n (m n) (P n) hn hm2 hnsize).trans hnPow

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
