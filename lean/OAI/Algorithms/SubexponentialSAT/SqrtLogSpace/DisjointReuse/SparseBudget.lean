import OAI.Algorithms.SubexponentialSAT.BranchTree
import OAI.Algorithms.SubexponentialSAT.Sunflower
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCharging
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Find
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Sharp numerical budgets for disjoint counting sparsification

The frozen counting manuscript, Appendix A, lines 1991–2054. These numerical lemmas do not assert the
existence of a sparsification tree or a primitive implementation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget

open Finset
open scoped BigOperators

/-- The literal-degree sum in the source's leaf occurrence estimate. -/
def occurrenceCap (k M : ℕ) : ℕ := 2 * ∑ j ∈ range k, M ^ j

theorem sum_pow_le_twice_last (M : ℕ) (hM : 2 ≤ M) (j : ℕ) :
    ∑ i ∈ range (j + 1), M ^ i ≤ 2 * M ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ]
    have hp : 2 * M ^ j ≤ M ^ (j + 1) := by
      rw [pow_succ]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right (M ^ j) hM
    omega

theorem occurrenceCap_le (k M : ℕ) (hk : 0 < k) (hM : 2 ≤ M) :
    occurrenceCap k M ≤ 4 * M ^ (k - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have h := sum_pow_le_twice_last M hM j
  dsimp [occurrenceCap]
  calc
    2 * ∑ i ∈ range (j + 1), M ^ i ≤ 2 * (2 * M ^ j) := Nat.mul_le_mul_left 2 h
    _ = 4 * M ^ (j + 1 - 1) := by simp; ring

/-- An explicit constant exponent absorbs the affine term in the dyadic test. -/
theorem control_exponent (a q γ : ℕ) :
    let T := 2 * (γ * (a + 4 * q + 1) + 1)
    1 ≤ T ∧ γ ≤ 2 ^ T ∧ γ * (a + q * (T + 2)) ≤ 2 ^ T := by
  let u := γ * (a + 4 * q + 1) + 1
  have hu : 1 ≤ u := by dsimp [u]; omega
  have hγ : γ ≤ u := by dsimp [u]; nlinarith
  have hconstant : γ * a + 2 * γ * q ≤ u := by dsimp [u]; nlinarith
  have hslope : 2 * γ * q + 1 ≤ u := by dsimp [u]; nlinarith
  have hp : u ≤ 2 ^ u := (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hsquare : u ^ 2 ≤ 2 ^ (2 * u) := by
    calc
      u ^ 2 ≤ (2 ^ u) ^ 2 := Nat.pow_le_pow_left hp 2
      _ = 2 ^ (2 * u) := by rw [← pow_mul, Nat.mul_comm]
  have hscaled := Nat.mul_le_mul_right u hslope
  have hlinear : γ * (a + q * (2 * u + 2)) ≤ u ^ 2 := by
    nlinarith
  refine ⟨by dsimp [u] at *; omega, ?_, hlinear.trans hsquare⟩
  exact hγ.trans ((by nlinarith : u ≤ u ^ 2).trans hsquare)

/-- A dyadic witness of order `s log s`, rather than the old quadratic witness.
The source's test uses `clog 2 (4 C M)`, so every comparison is integral. -/
theorem dyadic_witness (C : ℕ → ℕ) (a q γ s : ℕ) (hs : 0 < s)
    (hC : ∀ M, 2 ≤ M → C M ≤ a * M ^ q) :
    ∃ T e : ℕ, 1 ≤ T ∧ γ ≤ 2 ^ e ∧ 2 ≤ 2 ^ e ∧
      γ * Nat.clog 2 (4 * C (2 ^ e) * 2 ^ e) * s ≤ 2 ^ e ∧
      2 ^ e ≤ (4 * 2 ^ T) * s * (Nat.log 2 s + 1) ∧
      e ≤ T + 2 * (Nat.log 2 s + 1) ∧
      T = 2 * (γ * (a + 2 + 4 * (q + 1) + 1) + 1) := by
  let T := 2 * (γ * (a + 2 + 4 * (q + 1) + 1) + 1)
  let l := Nat.log 2 s + 1
  let t := Nat.log 2 l + 1
  let e := T + l + t
  obtain ⟨hT, hγT, hcontrol⟩ := control_exponent (a + 2) (q + 1) γ
  have hl : 0 < l := by dsimp [l]; omega
  have ht : t ≤ l := Nat.succ_le_of_lt (Nat.log_lt_self 2 (by omega))
  have hslow : s ≤ 2 ^ l := (Nat.lt_pow_succ_log_self (by decide) s).le
  have hllow : l ≤ 2 ^ t := (Nat.lt_pow_succ_log_self (by decide) l).le
  have hsup : 2 ^ l ≤ 2 * s := by
    calc
      2 ^ l = 2 ^ Nat.log 2 s * 2 := by rw [show l = Nat.log 2 s + 1 from rfl, pow_succ]
      _ ≤ s * 2 := Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 (by omega))
      _ = 2 * s := Nat.mul_comm _ _
  have htup : 2 ^ t ≤ 2 * l := by
    calc
      2 ^ t = 2 ^ Nat.log 2 l * 2 := by rw [show t = Nat.log 2 l + 1 from rfl, pow_succ]
      _ ≤ l * 2 := Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 (by omega))
      _ = 2 * l := Nat.mul_comm _ _
  have he : 1 ≤ e := by dsimp [e, T] at *; omega
  have hM : 2 ≤ 2 ^ e := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) he
  have hcoeff : 4 * a ≤ 2 ^ (a + 2) := by
    calc
      4 * a ≤ 4 * 2 ^ a := Nat.mul_le_mul_left 4 (Nat.lt_pow_self (by decide)).le
      _ = 2 ^ (a + 2) := by rw [pow_add]; norm_num; ring
  have hbase : 4 * C (2 ^ e) * 2 ^ e ≤ 2 ^ (a + 2 + (q + 1) * e) := by
    calc
      4 * C (2 ^ e) * 2 ^ e ≤ 4 * (a * (2 ^ e) ^ q) * 2 ^ e :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hC _ hM))
      _ = (4 * a) * (2 ^ e) ^ (q + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (a + 2) * (2 ^ e) ^ (q + 1) := Nat.mul_le_mul_right _ hcoeff
      _ = 2 ^ (a + 2 + (q + 1) * e) := by
        rw [← pow_mul, ← pow_add, Nat.mul_comm e (q + 1)]
  have hlog : Nat.clog 2 (4 * C (2 ^ e) * 2 ^ e) ≤ a + 2 + (q + 1) * e :=
    (Nat.le_pow_iff_clog_le (by decide)).mp hbase
  have htl : T ≤ T * l := Nat.le_mul_of_pos_right T hl
  have hal : a + 2 ≤ (a + 2) * l := Nat.le_mul_of_pos_right (a + 2) hl
  have het : e ≤ (T + 2) * l := by dsimp [e]; nlinarith
  have hbound : a + 2 + (q + 1) * e ≤ (a + 2 + (q + 1) * (T + 2)) * l := by
    have := Nat.mul_le_mul_left (q + 1) het
    nlinarith
  have hbudget : γ * Nat.clog 2 (4 * C (2 ^ e) * 2 ^ e) * s ≤ 2 ^ e := by
    calc
      γ * Nat.clog 2 (4 * C (2 ^ e) * 2 ^ e) * s ≤
          γ * ((a + 2 + (q + 1) * (T + 2)) * l) * s := by
        exact Nat.mul_le_mul_right s (Nat.mul_le_mul_left γ (hlog.trans hbound))
      _ = (γ * (a + 2 + (q + 1) * (T + 2))) * s * l := by ring
      _ ≤ 2 ^ T * s * l := by exact Nat.mul_le_mul_right l (Nat.mul_le_mul_right s hcontrol)
      _ ≤ 2 ^ T * 2 ^ l * 2 ^ t := Nat.mul_le_mul (Nat.mul_le_mul_left _ hslow) hllow
      _ = 2 ^ e := by
        calc
          2 ^ T * 2 ^ l * 2 ^ t = 2 ^ (T + l) * 2 ^ t :=
            congrArg (fun x : ℕ => x * 2 ^ t) (pow_add 2 T l).symm
          _ = 2 ^ e := (pow_add 2 (T + l) t).symm
  refine ⟨T, e, hT, ?_, hM, hbudget, ?_, ?_, rfl⟩
  · exact hγT.trans (Nat.pow_le_pow_right (by decide) (by dsimp [e]; omega))
  · calc
      2 ^ e = 2 ^ T * 2 ^ l * 2 ^ t := by dsimp [e]; rw [pow_add, pow_add]
      _ ≤ 2 ^ T * (2 * s) * (2 * l) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hsup) htup
      _ = (4 * 2 ^ T) * s * (Nat.log 2 s + 1) := by dsimp [l]; ring
  · dsimp [e]; omega

open SparseCharging

theorem depthConstant_le (k M : ℕ) (hM : 2 ≤ M) :
    depthConstant k M ≤ (4 * (k - 1) * 3 ^ (k - 2)) * M ^ (k - 2) := by
  have hsum : (∑ j ∈ range (k - 1), (3 * M) ^ j) ≤
      (k - 1) * (3 * M) ^ (k - 2) := by
    calc
      _ ≤ ∑ _j ∈ range (k - 1), (3 * M) ^ (k - 2) := by
        apply sum_le_sum
        intro j hj
        exact Nat.pow_le_pow_right (by omega) (by have := mem_range.mp hj; omega)
      _ = _ := by simp
  calc
    depthConstant k M ≤ 4 * ((k - 1) * (3 * M) ^ (k - 2)) := Nat.mul_le_mul_left _ hsum
    _ = _ := by rw [mul_pow]; ring

/-- Exact source test at the candidate `M = 2^e`, for the rational numerator `a`
and denominator `b`. Only integer arithmetic and a ceiling logarithm occur. -/
def parameterTest (k a b e : ℕ) : Bool :=
  decide (2 ≤ 2 ^ e ∧ rightConstant k ≤ 2 ^ e ∧
    rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * b ≤
      a * 2 ^ e)

/-- Conservative inverse of a positive rational budget. -/
def inverseIndex (a b : ℕ) : ℕ := (b - 1) / a + 1

theorem inverseIndex_mul (a b : ℕ) (ha : 0 < a) : b ≤ a * inverseIndex a b := by
  have := Nat.lt_mul_div_succ (b - 1) ha
  dsimp [inverseIndex]
  omega

/-- The search terminates, with a fully explicit coefficient depending only on
`k`. This theorem counts candidates; primitive bit costs are proved separately. -/
theorem exists_parameter (k a b : ℕ) (ha : 0 < a) :
    ∃ e, parameterTest k a b e = true := by
  let s := inverseIndex a b
  obtain ⟨T, e, _, hγ, hM, hbudget, _, _, _⟩ :=
    dyadic_witness (depthConstant k) (4 * (k - 1) * 3 ^ (k - 2)) (k - 2)
      (rightConstant k) s (by exact Nat.zero_lt_succ _)
      (fun M hM => depthConstant_le k M hM)
  refine ⟨e, ?_⟩
  simp only [parameterTest, decide_eq_true_eq]
  refine ⟨hM, hγ, ?_⟩
  calc
    rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * b ≤
        rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * (a * s) :=
      Nat.mul_le_mul_left _ (inverseIndex_mul a b ha)
    _ = a * (rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * s) := by ring
    _ ≤ a * 2 ^ e := Nat.mul_le_mul_left a hbudget

/-- First passing power of two in the source's deterministic search. -/
def chooseExponent (k a b : ℕ) (ha : 0 < a) : ℕ := Nat.find (exists_parameter k a b ha)

def chooseM (k a b : ℕ) (ha : 0 < a) : ℕ := 2 ^ chooseExponent k a b ha

theorem chooseExponent_spec (k a b : ℕ) (ha : 0 < a) :
    parameterTest k a b (chooseExponent k a b ha) = true :=
  Nat.find_spec (exists_parameter k a b ha)

theorem chooseExponent_le (k a b e : ℕ) (ha : 0 < a)
    (he : parameterTest k a b e = true) : chooseExponent k a b ha ≤ e :=
  Nat.find_min' (exists_parameter k a b ha) he

theorem chooseM_spec (k a b : ℕ) (ha : 0 < a) :
    2 ≤ chooseM k a b ha ∧ rightConstant k ≤ chooseM k a b ha ∧
      rightConstant k * Nat.clog 2 (4 * depthConstant k (chooseM k a b ha) *
        chooseM k a b ha) * b ≤ a * chooseM k a b ha := by
  simpa only [parameterTest, chooseM, decide_eq_true_eq] using chooseExponent_spec k a b ha

/-- The first successful candidate inherits the sharp witness bound. Constants
are chosen before the rational budget numerator and denominator. -/
theorem choose_bounds (k : ℕ) :
    ∃ K T : ℕ, ∀ a b (ha : 0 < a),
      chooseM k a b ha ≤ K * inverseIndex a b * (Nat.log 2 (inverseIndex a b) + 1) ∧
      chooseExponent k a b ha ≤ T + 2 * (Nat.log 2 (inverseIndex a b) + 1) := by
  let A := 4 * (k - 1) * 3 ^ (k - 2)
  let q := k - 2
  let T := 2 * (rightConstant k * (A + 2 + 4 * (q + 1) + 1) + 1)
  refine ⟨4 * 2 ^ T, T, ?_⟩
  intro a b ha
  let s := inverseIndex a b
  obtain ⟨T', e, _, hγ, hM, hbudget, hsize, hindex, hT⟩ :=
    dyadic_witness (depthConstant k) A q (rightConstant k) s
      (by exact Nat.zero_lt_succ _) (fun M hM => depthConstant_le k M hM)
  have he : parameterTest k a b e = true := by
    simp only [parameterTest, decide_eq_true_eq]
    refine ⟨hM, hγ, ?_⟩
    calc
      rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * b ≤
          rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * (a * s) :=
        Nat.mul_le_mul_left _ (inverseIndex_mul a b ha)
      _ = a * (rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * s) := by ring
      _ ≤ a * 2 ^ e := Nat.mul_le_mul_left a hbudget
  have hmin := chooseExponent_le k a b e ha he
  have hT' : T' = T := hT
  subst T'
  exact ⟨(Nat.pow_le_pow_right (by decide) hmin).trans hsize, hmin.trans hindex⟩

/-- The ceiling-log test implies the real exponent budget without a numerical
logarithm oracle. -/
theorem chooseM_log_budget (k a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (rightConstant k : ℝ) / chooseM k a b ha *
        Real.logb 2 (4 * (depthConstant k (chooseM k a b ha) : ℝ) * chooseM k a b ha) ≤
      (a : ℝ) / b := by
  let M := chooseM k a b ha
  obtain ⟨hM, _, htest⟩ := chooseM_spec k a b ha
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by dsimp [M]; omega)
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hceil : Real.logb 2 (4 * (depthConstant k M : ℝ) * M) ≤
      (Nat.clog 2 (4 * depthConstant k M * M) : ℝ) := by
    have h := Nat.le_ceil (Real.logb (2 : ℕ) (4 * depthConstant k M * M : ℕ))
    rw [Real.natCeil_logb_natCast 2 (4 * depthConstant k M * M)] at h
    simpa using h
  have ht : (rightConstant k : ℝ) * Nat.clog 2 (4 * depthConstant k M * M) * b ≤
      (a : ℝ) * M := by exact_mod_cast htest
  have hmul := mul_le_mul_of_nonneg_left hceil (by positivity : (0 : ℝ) ≤ rightConstant k)
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀ hMr hbr).mpr
  calc
    (rightConstant k : ℝ) * Real.logb 2 (4 * (depthConstant k M : ℝ) * M) * b ≤
        (rightConstant k : ℝ) * Nat.clog 2 (4 * depthConstant k M * M) * b :=
      mul_le_mul_of_nonneg_right hmul (by positivity)
    _ ≤ (a : ℝ) * M := ht

theorem inverseIndex_le (a b : ℕ) (ha : 0 < a) :
    (inverseIndex a b : ℝ) ≤ (b : ℝ) / a + 1 := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hdiv : (((b - 1) / a : ℕ) : ℝ) ≤ (b : ℝ) / a := by
    apply (le_div_iff₀ har).mpr
    exact_mod_cast (Nat.div_mul_le_self (b - 1) a).trans (Nat.sub_le b 1)
  simpa [inverseIndex] using add_le_add_right hdiv 1

/-- Sharp source asymptotics, with constants independent of both numerator and
 denominator. The logarithm is real base two. -/
theorem chooseM_real_bound (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ a b (ha : 0 < a), a ≤ b →
      (chooseM k a b ha : ℝ) ≤ K * ((b : ℝ) / a) * Real.logb 2 (2 * ((b : ℝ) / a)) := by
  obtain ⟨K, T, hK⟩ := choose_bounds k
  refine ⟨4 * (K + 1), by positivity, ?_⟩
  intro a b ha hab
  let r : ℝ := (b : ℝ) / a
  let s := inverseIndex a b
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hr : 1 ≤ r := by
    dsimp [r]
    exact (le_div_iff₀ har).mpr (by simpa using (Nat.cast_le (α := ℝ)).mpr hab)
  have hs : (0 : ℝ) < s := by dsimp [s, inverseIndex]; positivity
  have hsbound : (s : ℝ) ≤ 2 * r := by
    have := inverseIndex_le a b ha
    dsimp [s, r] at *
    linarith
  have hlog : (Nat.log 2 s : ℝ) ≤ Real.logb 2 (2 * r) :=
    (Real.natLog_le_logb s 2).trans (Real.logb_le_logb_of_le (by norm_num) hs hsbound)
  have hlogone : 1 ≤ Real.logb 2 (2 * r) := by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ 2 * r by linarith)
    simpa using h
  have hlogsum : (Nat.log 2 s : ℝ) + 1 ≤ 2 * Real.logb 2 (2 * r) := by linarith
  have hsize : (chooseM k a b ha : ℝ) ≤ (K : ℝ) * s * ((Nat.log 2 s : ℝ) + 1) := by
    exact_mod_cast (hK a b ha).1
  calc
    (chooseM k a b ha : ℝ) ≤ (K : ℝ) * s * ((Nat.log 2 s : ℝ) + 1) := hsize
    _ ≤ (K : ℝ) * (2 * r) * (2 * Real.logb 2 (2 * r)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hsbound (by positivity)
      · exact hlogsum
      · positivity
      · positivity
    _ ≤ 4 * (K + 1) * r * Real.logb 2 (2 * r) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ r) (by linarith : 0 ≤ Real.logb 2 (2 * r))]

theorem rational_data (σ : ℚ) (hσ : 0 < σ) :
    0 < σ.num.natAbs ∧ (σ.num.natAbs : ℝ) / σ.den = (σ : ℝ) := by
  have hnum : 0 < σ.num := Rat.num_pos.mpr hσ
  have habs : (σ.num.natAbs : ℤ) = σ.num := Int.natAbs_of_nonneg hnum.le
  refine ⟨Int.natAbs_pos.mpr (ne_of_gt hnum), ?_⟩
  rw [Rat.cast_def]
  congr 1
  simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) habs

/-- The source selector on a positive rational budget, preserving its exact
numerator and denominator in every comparison. -/
def chooseForSigma (k : ℕ) (σ : ℚ) (hσ : 0 < σ) : ℕ :=
  chooseM k σ.num.natAbs σ.den (rational_data σ hσ).1

theorem chooseForSigma_reciprocal (k s : ℕ) (hs : 0 < s)
    (hσ : (0 : ℚ) < 1 / s) :
    chooseForSigma k (1 / s) hσ = chooseM k 1 s (by decide) := by
  have hn : ((1 : ℚ) / s).num = 1 := by
    simpa only [Int.cast_one, Int.cast_natCast] using
      Rat.num_div_eq_of_coprime (a := 1) (b := (s : ℤ))
      (by exact_mod_cast hs) (by simp)
  have hd : ((1 : ℚ) / s).den = s := by
    have hd' : (((1 : ℚ) / s).den : ℤ) = (s : ℤ) := by
      simpa only [Int.cast_one, Int.cast_natCast] using Rat.den_div_eq_of_coprime
        (a := 1) (b := (s : ℤ)) (by exact_mod_cast hs) (by simp)
    exact_mod_cast hd'
  simp only [chooseForSigma, hn, hd, Int.natAbs_one]

theorem chooseForSigma_log_budget (k : ℕ) (σ : ℚ) (hσ : 0 < σ) :
    (rightConstant k : ℝ) / chooseForSigma k σ hσ *
        Real.logb 2 (4 * (depthConstant k (chooseForSigma k σ hσ) : ℝ) *
          chooseForSigma k σ hσ) ≤ (σ : ℝ) := by
  simpa only [chooseForSigma, (rational_data σ hσ).2] using
    chooseM_log_budget k σ.num.natAbs σ.den (rational_data σ hσ).1 σ.pos

theorem chooseForSigma_sharp (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (σ : ℚ) (hσ : 0 < σ), σ ≤ 1 →
      (chooseForSigma k σ hσ : ℝ) ≤
        K * (σ : ℝ)⁻¹ * Real.logb 2 (2 / (σ : ℝ)) := by
  obtain ⟨K, hK, hbound⟩ := chooseM_real_bound k
  refine ⟨K, hK, ?_⟩
  intro σ hσ hσone
  have hdata := rational_data σ hσ
  have hden : (0 : ℝ) < σ.den := by exact_mod_cast σ.pos
  have hσreal : (σ : ℝ) ≤ 1 := by exact_mod_cast hσone
  have hab : σ.num.natAbs ≤ σ.den := by
    rw [← hdata.2, div_le_one hden] at hσreal
    exact_mod_cast hσreal
  have hinv : (σ.den : ℝ) / σ.num.natAbs = (σ : ℝ)⁻¹ := by
    rw [← hdata.2, inv_div]
  simpa only [chooseForSigma, hinv, div_eq_mul_inv] using
    hbound σ.num.natAbs σ.den hdata.1 hab

/-- The source's explicit node bound for a tree with the charged path budgets.
It applies to an actual finite tree and includes every internal node. -/
theorem nodeCount_le (t : BranchTree.Tree) (C γ n M : ℕ) (σ : ℝ)
    (hC : 1 ≤ C) (hγ : 1 ≤ γ) (hγM : γ ≤ M)
    (hbudget : (γ : ℝ) / M * Real.logb 2 (4 * (C : ℝ) * M) ≤ σ)
    (hdepth : ∀ p ∈ t.paths, p.length ≤ C * n)
    (hB : ∀ p ∈ t.paths, p.count true ≤ γ * n / M) :
    (t.nodeCount : ℝ) ≤ ((C * n + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (σ * n) := by
  have hpositions : ∀ p ∈ t.paths, (BranchTree.bPositions p).card ≤ γ * n / M := by
    intro p hp
    rw [BranchTree.card_bPositions_eq_count]
    exact hB p hp
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hγpos : (0 : ℝ) < γ := by exact_mod_cast (show 0 < γ by omega)
  have hγone : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
  have hCpos : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hdim : (γ : ℝ) / M ≤ C := by
    have hquot : (γ : ℝ) / M ≤ 1 := (div_le_one hM).mpr (by exact_mod_cast hγM)
    exact hquot.trans (by exact_mod_cast hC)
  by_cases hn : n = 0
  · subst n
    have ht := t.nodeCount_le (C * 0) (γ * 0 / M) hdepth hpositions
    have ht' : t.nodeCount ≤ 1 := by simpa using ht
    simpa using (Nat.cast_le (α := ℝ)).mpr ht'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  let q : ℝ := (γ : ℝ) * n / M
  have hq : 0 < q := by dsimp [q]; positivity
  have hD : q ≤ (C * n : ℕ) := by
    have h := mul_le_mul_of_nonneg_right hdim hnpos.le
    simpa [q, Nat.cast_mul, div_mul_eq_mul_div] using h
  have hR : ((γ * n / M : ℕ) : ℝ) ≤ q := by
    simpa [q, Nat.cast_mul] using (Nat.cast_div_le (m := γ * n) (n := M) (α := ℝ))
  have hbase : 4 * ((C * n : ℕ) : ℝ) / q = 4 * (C : ℝ) * M / γ := by
    dsimp [q]
    push_cast
    field_simp
  have hlog : Real.logb 2 (4 * (C : ℝ) * M / γ) ≤ Real.logb 2 (4 * (C : ℝ) * M) := by
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    exact div_le_self (by positivity) hγone
  have hb : (γ : ℝ) / M * Real.log (4 * (C : ℝ) * M / γ) ≤ Real.log 2 * σ := by
    have hh := (mul_le_mul_of_nonneg_left hlog
      (by positivity : (0 : ℝ) ≤ (γ : ℝ) / M)).trans hbudget
    rw [Real.logb, ← mul_div_assoc, div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))] at hh
    simpa [mul_comm] using hh
  have hbudget' : q * Real.log (4 * ((C * n : ℕ) : ℝ) / q) ≤ Real.log 2 * (σ * n) := by
    rw [hbase]
    have hh := mul_le_mul_of_nonneg_right hb hnpos.le
    convert hh using 1 <;> (try dsimp [q]) <;> ring
  have ht := BranchTree.card_paths_le_two_rpow t.paths (C * n) (γ * n / M)
    hq hD hR hdepth hpositions hbudget'
  rw [t.card_paths] at ht
  have hquot : γ * n / M ≤ C * n := by
    calc
      γ * n / M ≤ n := Nat.div_le_of_le_mul (by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right n hγM)
      _ ≤ C * n := by nlinarith
  have hquotr : ((γ * n / M : ℕ) : ℝ) + 1 ≤ (C * n : ℕ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hquot 1
  refine ht.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by norm_num) _))
  simpa only [Nat.cast_add, Nat.cast_one, pow_two] using
    mul_le_mul_of_nonneg_left hquotr (by positivity : (0 : ℝ) ≤ (C * n : ℕ) + 1)

theorem four_le_depthConstant (k M : ℕ) (hk : 2 ≤ k) : 4 ≤ depthConstant k M := by
  have hsum : 1 ≤ ∑ j ∈ range (k - 1), (3 * M) ^ j := by
    simpa using (Finset.single_le_sum (f := fun j => (3 * M) ^ j)
      (fun _ _ => Nat.zero_le _) (show 0 ∈ range (k - 1) from mem_range.mpr (by omega)))
  exact Nat.mul_le_mul_left 4 hsum

theorem four_le_rightConstant (k : ℕ) (hk : 2 ≤ k) : 4 ≤ rightConstant k := by
  simpa [depthConstant, rightConstant] using four_le_depthConstant k 1 hk

theorem selected_nodeCount_le (t : BranchTree.Tree) (k n : ℕ) (σ : ℚ)
    (hk : 2 ≤ k) (hσ : 0 < σ)
    (hdepth : ∀ p ∈ t.paths, p.length ≤ depthConstant k (chooseForSigma k σ hσ) * n)
    (hB : ∀ p ∈ t.paths, p.count true ≤ rightConstant k * n / chooseForSigma k σ hσ) :
    (t.nodeCount : ℝ) ≤
      ((depthConstant k (chooseForSigma k σ hσ) * n + 1 : ℕ) : ℝ) ^ 2 *
        (2 : ℝ) ^ ((σ : ℝ) * n) := by
  have hspec := chooseM_spec k σ.num.natAbs σ.den (rational_data σ hσ).1
  exact nodeCount_le t (depthConstant k (chooseForSigma k σ hσ)) (rightConstant k)
    n (chooseForSigma k σ hσ) σ
    (by have := four_le_depthConstant k (chooseForSigma k σ hσ) hk; omega)
    (by have := four_le_rightConstant k hk; omega) hspec.2.1
    (chooseForSigma_log_budget k σ hσ) hdepth hB

/-- Terminality of the actual priority selector gives the sharp occurrence cap.
Unused variables contribute zero occurrences and are retained in the ambient type. -/
theorem leaf_occurrences_le {n : ℕ} (F : SAT.CNF (Fin n)) (k M : ℕ)
    (hM : 2 ≤ M) (hWidth : ∀ C ∈ F, C.card ≤ k)
    (hTerminal : SparsePriority.select F M = none) :
    ∀ v, SAT.occurrences v F ≤ occurrenceCap k M := by
  apply Sunflower.variable_occurrence_le_of_literal_bound F
    (∑ j ∈ range k, M ^ j)
  intro x
  calc
    (F.filter (fun C => x ∈ C)).card ≤
        ∑ j ∈ range (k + 1), if j = 0 then 0 else M ^ (j - 1) := by
      apply Sunflower.literal_total_occurrence_le F k _ x hWidth
      intro j _
      rcases j with _ | j
      · have hempty : F.filter (fun C => C.card = 0 ∧ x ∈ C) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro C hC
          obtain ⟨_, hc, hx⟩ := Finset.mem_filter.mp hC
          rw [Finset.card_eq_zero.mp hc] at hx
          simp at hx
        rw [hempty]
        simp
      · cases j with
        | zero => simpa using Sunflower.unit_literal_occurrence_le F x
        | succ j =>
          have hd := SparsePriority.select_none_degree_lt (F := F) (M := M)
            (c := j + 1 + 1) (H := {x}) (by omega) hTerminal (by simp) (by simp)
          simpa [SparsePriority.degree, DisjointBranch.selected] using hd.le
    _ = ∑ j ∈ range k, M ^ j := by rw [Finset.sum_range_succ']; simp

theorem leaf_occurrences_le_power {n : ℕ} (F : SAT.CNF (Fin n)) (k M : ℕ)
    (hk : 0 < k) (hM : 2 ≤ M) (hWidth : ∀ C ∈ F, C.card ≤ k)
    (hTerminal : SparsePriority.select F M = none) :
    ∀ v, SAT.occurrences v F ≤ 4 * M ^ (k - 1) := by
  intro v
  exact (leaf_occurrences_le F k M hM hWidth hTerminal v).trans (occurrenceCap_le k M hk hM)

/-- Concrete finite scanning of the exact Boolean tests. This counts test calls,
not primitive bit operations. -/
theorem choose_finite_scan (k a b : ℕ) (ha : 0 < a) :
    ParameterOrder.scanFrom (parameterTest k a b) 0 (chooseExponent k a b ha + 1) =
      (some (chooseExponent k a b ha), chooseExponent k a b ha + 1) := by
  simpa only [ParameterOrder.select, chooseExponent] using
    ParameterOrder.select_bounded_execution (parameterTest k a b) (exists_parameter k a b ha)
      (chooseExponent_spec k a b ha)

theorem inverseIndex_le_denominator (a b : ℕ) (hb : 0 < b) : inverseIndex a b ≤ b := by
  have := Nat.div_le_self (b - 1) a
  dsimp [inverseIndex]
  omega

/-- Search length is logarithmic in the positive rational denominator; candidate
values remain polynomial in it. This exposes the uniform parameter-size budget. -/
theorem choose_encoding_bounds (k : ℕ) :
    ∃ K T : ℕ, ∀ a b (ha : 0 < a), 0 < b →
      chooseM k a b ha ≤ K * b ^ 2 ∧
      chooseExponent k a b ha ≤ T + 2 * (Nat.log 2 b + 1) := by
  obtain ⟨K, T, h⟩ := choose_bounds k
  refine ⟨K, T, ?_⟩
  intro a b ha hb
  have hs := inverseIndex_le_denominator a b hb
  have hlog : Nat.log 2 (inverseIndex a b) + 1 ≤ inverseIndex a b :=
    Nat.succ_le_of_lt (Nat.log_lt_self 2 (by exact Nat.succ_ne_zero _))
  constructor
  · calc
      chooseM k a b ha ≤ K * inverseIndex a b * (Nat.log 2 (inverseIndex a b) + 1) :=
        (h a b ha).1
      _ ≤ K * b * b := Nat.mul_le_mul (Nat.mul_le_mul_left K hs) (hlog.trans hs)
      _ = K * b ^ 2 := by ring
  · exact (h a b ha).2.trans (by have := Nat.log_mono_right (b := 2) hs; omega)

/-- Discharge the numeric path premises from actual priority-selected paths. -/
theorem selectedPaths_nodeCount_le {n : ℕ} (t : BranchTree.Tree)
    (F : SAT.CNF (Fin n)) (k : ℕ) (σ : ℚ) (hk : 2 ≤ k) (hσ : 0 < σ)
    (hanti : SunflowerBranch.Antichain F)
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) (hwidth : SAT.WidthAtMost k F)
    (hpaths : ∀ p ∈ t.paths, ∃ G, SelectedPath (chooseForSigma k σ hσ) F p G) :
    (t.nodeCount : ℝ) ≤
      ((depthConstant k (chooseForSigma k σ hσ) * n + 1 : ℕ) : ℝ) ^ 2 *
        (2 : ℝ) ^ ((σ : ℝ) * n) := by
  have hM : 2 ≤ chooseForSigma k σ hσ :=
    (chooseM_spec k σ.num.natAbs σ.den (rational_data σ hσ).1).1
  apply selected_nodeCount_le t k n σ hk hσ
  · intro p hp
    obtain ⟨G, hG⟩ := hpaths p hp
    exact hG.length_le hM hanti hnt hwidth
  · intro p hp
    obtain ⟨G, hG⟩ := hpaths p hp
    exact (Nat.le_div_iff_mul_le (by omega)).mpr
      (hG.count_true_mul_le hM hanti hnt hwidth)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget
