import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration
import OAI.Algorithms.SubexponentialSAT.DyadicSchedule
import OAI.Algorithms.SubexponentialSAT.SubexpRuntime

namespace OAI.Algorithms

/-!
# The actual masked tuple search at the dyadic threshold

The budget is the proved instruction count of ExecCNFTupleEnumeration,
including every callback, rejected candidate, and final overflow increment.
A fixed polynomial bound on the actual callback is kept explicit. It is not
replaced by the older sparsifier's semantic list-event pricing.
-/

namespace SubexponentialSAT.DyadicMaskedSearchBounds

open Filter
open SubexpPackingParameters
open SparsificationConstants

def localSize (n m r k : ℕ) : ℕ := n + m + r + k + 1

def sourceBudget (k m r callback : ℕ) : ℕ :=
  2 ^ k * (2 * (m + 1)) ^ r *
    (callback + 14 * (k + r * DyadicWidth.width m) + 14 * (r + 1) + 12) + 3

def searchDegree (k a r : ℕ) : ℕ :=
  k + (2 * k + 2) * r + ((2 * k + 3) * (a + 2) + 3)

def threshold (k T n : ℕ) : ℕ :=
  SparsificationBudget.thresholdCap (DyadicSchedule.M T n) k

def arity (T n j : ℕ) : ℕ := z (DyadicSchedule.M T n) j

theorem arity_le_threshold (k T n j : ℕ) (hj : j ≤ k) :
    arity T n j ≤ threshold k T n :=
  SparsificationBudget.z_le_thresholdCap _ _ _ hj

theorem localSize_le_power {n m r k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n)
    (hr : r ≤ n) (hm : m ≤ (2 * n + 1) ^ k) :
    localSize n m r k ≤ (n + 1) ^ (2 * k + 3) := by
  have hb : 1 ≤ n + 1 := by omega
  have hbase : 2 * n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have hm' : m ≤ (n + 1) ^ (2 * k) := by
    calc
      m ≤ (2 * n + 1) ^ k := hm
      _ ≤ ((n + 1) ^ 2) ^ k := Nat.pow_le_pow_left hbase k
      _ = _ := by rw [← pow_mul]
  have hsmall : n + 1 ≤ (n + 1) ^ (2 * k + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < n + 1)
      (by omega : 1 ≤ 2 * k + 1)
  have hm'' : m ≤ (n + 1) ^ (2 * k + 1) :=
    hm'.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hlocal : localSize n m r k ≤ 4 * (n + 1) ^ (2 * k + 1) := by
    unfold localSize
    omega
  have hfour : 4 ≤ (n + 1) ^ 2 := by nlinarith
  calc
    _ ≤ 4 * (n + 1) ^ (2 * k + 1) := hlocal
    _ ≤ (n + 1) ^ 2 * (n + 1) ^ (2 * k + 1) :=
      Nat.mul_le_mul_right _ hfour
    _ = (n + 1) ^ (2 * k + 3) := by rw [← pow_add]; congr 1; omega

theorem callback_plus_counter_le {n m r k C a callback : ℕ}
    (hcallback : callback ≤ C * localSize n m r k ^ a) :
    callback + 14 * (k + r * DyadicWidth.width m) + 14 * (r + 1) + 12 ≤
      (C + 54) * localSize n m r k ^ (a + 2) := by
  let L := localSize n m r k
  have hL : 1 ≤ L := by dsimp [L, localSize]; omega
  have hk : k ≤ L := by dsimp [L, localSize]; omega
  have hr : r ≤ L := by dsimp [L, localSize]; omega
  have hr1 : r + 1 ≤ L := by dsimp [L, localSize]; omega
  have hm : m + 1 ≤ L := by dsimp [L, localSize]; omega
  have hw : DyadicWidth.width m ≤ L := (DyadicWidth.width_le_succ m).trans hm
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have hp2 : 1 ≤ L ^ 2 := Nat.one_le_pow _ _ hL
  have hprod : r * DyadicWidth.width m ≤ L ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hr hw
  have hcounter : 14 * (k + r * DyadicWidth.width m) + 14 * (r + 1) + 12 ≤
      54 * L ^ 2 := by omega
  have hpa : L ^ a ≤ L ^ (a + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hp22 : L ^ 2 ≤ L ^ (a + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hc : callback ≤ C * L ^ (a + 2) :=
    hcallback.trans (Nat.mul_le_mul_left C hpa)
  have hcount : 14 * (k + r * DyadicWidth.width m) + 14 * (r + 1) + 12 ≤
      54 * L ^ (a + 2) := hcounter.trans (Nat.mul_le_mul_left 54 hp22)
  change _ ≤ (C + 54) * L ^ (a + 2)
  nlinarith

theorem tuple_count_le_power {n m k r : ℕ} (hn : 1 ≤ n)
    (hm : m ≤ (2 * n + 1) ^ k) :
    2 ^ k * (2 * (m + 1)) ^ r ≤ (n + 1) ^ (k + (2 * k + 2) * r) := by
  have hb : 2 ≤ n + 1 := by omega
  have hbase : 2 * n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have hm' : m ≤ (n + 1) ^ (2 * k) := by
    calc
      _ ≤ ((n + 1) ^ 2) ^ k := hm.trans (Nat.pow_le_pow_left hbase k)
      _ = _ := by rw [← pow_mul]
  have hp : 1 ≤ (n + 1) ^ (2 * k) := Nat.one_le_pow _ _ (by omega)
  have hfour : 4 ≤ (n + 1) ^ 2 := by nlinarith
  have hchoices : 2 * (m + 1) ≤ (n + 1) ^ (2 * k + 2) := by
    calc
      _ ≤ 4 * (n + 1) ^ (2 * k) := by omega
      _ ≤ (n + 1) ^ 2 * (n + 1) ^ (2 * k) := Nat.mul_le_mul_right _ hfour
      _ = _ := by rw [← pow_add]; congr 1; omega
  calc
    _ ≤ (n + 1) ^ k * ((n + 1) ^ (2 * k + 2)) ^ r :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hb k) (Nat.pow_le_pow_left hchoices r)
    _ = _ := by rw [← pow_mul, ← pow_add]

theorem sourceBudget_le_power {n m r k C a callback : ℕ}
    (hn : 1 ≤ n) (hk : k ≤ n) (hC : C + 54 ≤ n + 1) (hr : r ≤ n)
    (hm : m ≤ (2 * n + 1) ^ k)
    (hcallback : callback ≤ C * localSize n m r k ^ a) :
    sourceBudget k m r callback ≤ (n + 1) ^ searchDegree k a r := by
  have hlocal := localSize_le_power hn hk hr hm
  have hcounter := callback_plus_counter_le hcallback
  have hbracket :
      callback + 14 * (k + r * DyadicWidth.width m) + 14 * (r + 1) + 12 ≤
        (n + 1) ^ (1 + (2 * k + 3) * (a + 2)) := by
    calc
      _ ≤ (C + 54) * localSize n m r k ^ (a + 2) := hcounter
      _ ≤ (n + 1) * ((n + 1) ^ (2 * k + 3)) ^ (a + 2) :=
        Nat.mul_le_mul hC (Nat.pow_le_pow_left hlocal (a + 2))
      _ = _ := by rw [← pow_mul, pow_add, pow_one]
  let e := k + (2 * k + 2) * r + (1 + (2 * k + 3) * (a + 2))
  have hwork : 2 ^ k * (2 * (m + 1)) ^ r *
      (callback + 14 * (k + r * DyadicWidth.width m) + 14 * (r + 1) + 12) ≤
        (n + 1) ^ e := by
    have h := Nat.mul_le_mul (tuple_count_le_power (r := r) hn hm) hbracket
    simpa only [e, ← pow_add] using h
  have hp : 1 ≤ (n + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  have hfour : 4 ≤ (n + 1) ^ 2 := by nlinarith
  calc
    sourceBudget k m r callback ≤ (n + 1) ^ e + 3 := Nat.add_le_add_right hwork 3
    _ ≤ 4 * (n + 1) ^ e := by omega
    _ ≤ (n + 1) ^ 2 * (n + 1) ^ e := Nat.mul_le_mul_right _ hfour
    _ = (n + 1) ^ searchDegree k a r := by
      rw [← pow_add]
      congr 1
      dsimp [e, searchDegree]
      omega

theorem threshold_eventually_le_n (k T : ℕ) :
    ∀ᶠ n : ℕ in atTop, threshold k T n ≤ n := by
  have hcap := (SparsificationBudgetProgram.dyadicThresholdCap_polynomialBound T k).eventually_le_two_pow
  filter_upwards [tendsto_s_atTop.eventually hcap, eventually_goodInput] with n hn hg
  calc
    threshold k T n ≤ 2 ^ s n := hn
    _ ≤ Nat.log2 n := pow_s_le_log2 (goodInput_two_le hg)
    _ ≤ n := Nat.log2_le_self n

theorem searchDegree_polynomialBound (k T a : ℕ) :
    PolynomialBound (fun s => searchDegree k a
      (SparsificationBudget.thresholdCap (SparsificationBudgetProgram.dyadicM T s) k)) := by
  unfold searchDegree
  exact ((polynomialBound_const k).add
    ((polynomialBound_const (2 * k + 2)).mul
      (SparsificationBudgetProgram.dyadicThresholdCap_polynomialBound T k))).add
    (polynomialBound_const ((2 * k + 3) * (a + 2) + 3))

theorem searchPower_subexponential (k T a : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (((n + 1) ^ searchDegree k a (threshold k T n) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ SubexpComputation.scale n := by
  obtain ⟨C, d, hb⟩ := searchDegree_polynomialBound k T a
  have he : ∀ᶠ n : ℕ in atTop,
      (searchDegree k a (threshold k T n) : ℝ) ≤
        ((C + 1 : ℕ) : ℝ) * ((s n : ℝ) + 2) ^ d := by
    filter_upwards [eventually_goodInput] with n hn
    have hs : 2 ≤ s n := by unfold GoodInput at hn; omega
    have h := (hb (s n) hs).trans
      (Nat.mul_le_mul (Nat.le_succ C) (Nat.pow_le_pow_left (by omega : s n ≤ s n + 2) d))
    exact_mod_cast h
  exact SubexpRuntime.eventually_variable_degree_search
    (fun n => searchDegree k a (threshold k T n)) d (by positivity) he

/-- One bound applies to every arity j <= k and every width-bounded formula
at every sufficiently large input size. Only the actual callback's fixed
local-polynomial execution bound remains as a premise. -/
theorem eventually_sourceBudget_le_power (k T C a : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, j ≤ k → ∀ m callback : ℕ,
      m ≤ (2 * n + 1) ^ k →
      callback ≤ C * localSize n m (arity T n j) k ^ a →
      sourceBudget k m (arity T n j) callback ≤
        (n + 1) ^ searchDegree k a (threshold k T n) := by
  filter_upwards [threshold_eventually_le_n k T, eventually_ge_atTop (1 : ℕ),
    eventually_ge_atTop k, eventually_ge_atTop (C + 54)] with n hthreshold hn hk hC
  intro j hj m callback hm hcallback
  have hr := arity_le_threshold k T n j hj
  have hs := sourceBudget_le_power hn hk (by omega) (hr.trans hthreshold) hm hcallback
  have hmul := Nat.mul_le_mul_left (2 * k + 2) hr
  exact hs.trans (Nat.pow_le_pow_right (by omega) (by dsimp [searchDegree]; omega))

theorem eventually_sourceBudget_subexponential (k T C a : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, j ≤ k → ∀ m callback : ℕ,
      m ≤ (2 * n + 1) ^ k →
      callback ≤ C * localSize n m (arity T n j) k ^ a →
      (sourceBudget k m (arity T n j) callback : ℝ) ≤
        (2 : ℝ) ^ SubexpComputation.scale n := by
  filter_upwards [eventually_sourceBudget_le_power k T C a,
    searchPower_subexponential k T a] with n hsource hpower j hj m callback hm hc
  exact (Nat.cast_le.mpr (hsource j hj m callback hm hc)).trans hpower

end SubexponentialSAT.DyadicMaskedSearchBounds

end OAI.Algorithms
