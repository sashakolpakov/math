import OAI.Algorithms.SubexponentialSAT.SqrtLog.StatementScale
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Sqrt

/-! Numerical parameters for the disjoint counting reduction. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- The literal base-two exponent in the counting manuscript. -/
noncomputable def rho (n : ℕ) : ℝ :=
  (n : ℝ) * (Real.logb 2 (Real.logb 2 n)) ^ 2 / Real.sqrt (Real.logb 2 n)

/-- Exact ceiling logarithms, computed with natural-number arithmetic. -/
def sparsifyLambda (n : ℕ) : ℕ := Nat.clog 2 n

def sparsifyNu (n : ℕ) : ℕ := Nat.clog 2 (sparsifyLambda n)

def sparsifySchedule (n : ℕ) : ℕ :=
  Nat.sqrt (sparsifyLambda n) / sparsifyNu n ^ 2

theorem sparsifyLambda_eq_ceil (n : ℕ) :
    sparsifyLambda n = ⌈Real.logb 2 n⌉₊ :=
  (Real.natCeil_logb_natCast 2 n).symm

theorem sparsifyNu_eq_ceil (n : ℕ) :
    sparsifyNu n = ⌈Real.logb 2 (sparsifyLambda n)⌉₊ :=
  (Real.natCeil_logb_natCast 2 (sparsifyLambda n)).symm

theorem sparsifyNu_pos {n : ℕ} (hn : 20 ≤ n) : 0 < sparsifyNu n := by
  have hLambda : 2 ≤ sparsifyLambda n := by
    have h := (Nat.pow_lt_iff_lt_clog (by norm_num : 1 < (2 : ℕ))).mp
      (show 2 ^ 1 < n by omega)
    exact h
  exact Nat.clog_pos (by norm_num) hLambda

theorem le_sparsifySchedule_iff {n : ℕ} (hn : 20 ≤ n) (a : ℕ) :
    a ≤ sparsifySchedule n ↔ a ^ 2 * sparsifyNu n ^ 4 ≤ sparsifyLambda n := by
  rw [sparsifySchedule, Nat.le_div_iff_mul_le (pow_pos (sparsifyNu_pos hn) 2),
    Nat.le_sqrt']
  ring_nf

theorem sparsifySchedule_feasible {n : ℕ} (hn : 20 ≤ n) :
    sparsifySchedule n ^ 2 * sparsifyNu n ^ 4 ≤ sparsifyLambda n :=
  (le_sparsifySchedule_iff hn _).mp le_rfl

theorem sparsifySchedule_maximal {n : ℕ} (hn : 20 ≤ n) :
    sparsifyLambda n < (sparsifySchedule n + 1) ^ 2 * sparsifyNu n ^ 4 := by
  have h := (le_sparsifySchedule_iff hn (sparsifySchedule n + 1)).not
  exact Nat.lt_of_not_ge (h.mp (by omega))

theorem sparsifySchedule_le_lambda (n : ℕ) : sparsifySchedule n ≤ sparsifyLambda n :=
  (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)

theorem sparsifyLambda_le_log2_shift (n : ℕ) :
    sparsifyLambda n ≤ Nat.log2 (n + 16) + 1 := by
  apply (Nat.le_pow_iff_clog_le (by norm_num : 1 < (2 : ℕ))).mp
  exact (Nat.le_add_right n 16).trans Nat.lt_log2_self.le

theorem sparsify_parameters_le_input (n : ℕ) :
    sparsifyLambda n ≤ n ∧ sparsifyNu n ≤ n ∧ sparsifySchedule n ≤ n := by
  have hLambda : sparsifyLambda n ≤ n :=
    (Nat.le_pow_iff_clog_le (by norm_num : 1 < (2 : ℕ))).mp Nat.lt_two_pow_self.le
  have hNu : sparsifyNu n ≤ sparsifyLambda n :=
    (Nat.le_pow_iff_clog_le (by norm_num : 1 < (2 : ℕ))).mp Nat.lt_two_pow_self.le
  exact ⟨hLambda, hNu.trans hLambda, (sparsifySchedule_le_lambda n).trans hLambda⟩

theorem four_le_logb {n : ℕ} (hn : 20 ≤ n) : 4 ≤ Real.logb 2 n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (show 0 < n by omega))).mpr
  norm_num
  exact_mod_cast (show 16 ≤ n by omega)

theorem sparsifyLambda_bounds {n : ℕ} (hn : 20 ≤ n) :
    Real.logb 2 n ≤ (sparsifyLambda n : ℝ) ∧
      (sparsifyLambda n : ℝ) ≤ 2 * Real.logb 2 n := by
  rw [sparsifyLambda_eq_ceil]
  have h := four_le_logb hn
  exact ⟨Nat.le_ceil _, by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ Real.logb 2 n)
    linarith⟩

theorem sparsifyNu_le {n : ℕ} (hn : 20 ≤ n) :
    (sparsifyNu n : ℝ) ≤ 2 * Real.logb 2 (Real.logb 2 n) := by
  have hl := four_le_logb hn
  have hl0 : 0 < Real.logb 2 n := by linarith
  have hLambda := sparsifyLambda_bounds hn
  have hLambda0 : 0 < (sparsifyLambda n : ℝ) := by linarith
  have hv : 2 ≤ Real.logb 2 (Real.logb 2 n) := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hl0).mpr
    norm_num
    exact hl
  have hlog : Real.logb 2 (sparsifyLambda n) ≤ 1 + Real.logb 2 (Real.logb 2 n) := by
    calc
      _ ≤ Real.logb 2 (2 * Real.logb 2 n) :=
        Real.logb_le_logb_of_le (by norm_num) hLambda0 hLambda.2
      _ = _ := by rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) hl0.ne']; norm_num
  have hlog0 : 0 ≤ Real.logb 2 (sparsifyLambda n) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  rw [sparsifyNu_eq_ceil]
  have := Nat.ceil_lt_add_one hlog0
  linarith

theorem inverse_sparsifySchedule_le {n : ℕ} (hn : 20 ≤ n)
    (hs : 1 ≤ sparsifySchedule n) : (n : ℝ) / sparsifySchedule n ≤ 8 * rho n := by
  have hl := four_le_logb hn
  have hl0 : 0 < Real.logb 2 n := by linarith
  have hLambda := (sparsifyLambda_bounds hn).1
  have hm : (sparsifyLambda n : ℝ) <
      ((sparsifySchedule n : ℝ) + 1) ^ 2 * (sparsifyNu n : ℝ) ^ 4 := by
    exact_mod_cast sparsifySchedule_maximal hn
  have hroot : Real.sqrt (Real.logb 2 n) ≤
      ((sparsifySchedule n : ℝ) + 1) * (sparsifyNu n : ℝ) ^ 2 := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (sparsifyLambda n : ℝ) := hLambda
      _ ≤ ((sparsifySchedule n : ℝ) + 1) ^ 2 * (sparsifyNu n : ℝ) ^ 4 := hm.le
      _ = _ := by ring_nf
  have hv : 0 ≤ Real.logb 2 (Real.logb 2 n) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hnu := sparsifyNu_le hn
  have hnu2 : (sparsifyNu n : ℝ) ^ 2 ≤
      4 * (Real.logb 2 (Real.logb 2 n)) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (sparsifyNu n)]
  have hs' : (1 : ℝ) ≤ sparsifySchedule n := by exact_mod_cast hs
  have hroot' : Real.sqrt (Real.logb 2 n) ≤
      8 * (sparsifySchedule n : ℝ) * (Real.logb 2 (Real.logb 2 n)) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hnu2
      (show 0 ≤ (sparsifySchedule n : ℝ) + 1 by positivity)
    nlinarith [sq_nonneg (Real.logb 2 (Real.logb 2 n))]
  unfold rho
  rw [show 8 * ((n : ℝ) * (Real.logb 2 (Real.logb 2 n)) ^ 2 /
      Real.sqrt (Real.logb 2 n)) =
    (8 * (n : ℝ) * (Real.logb 2 (Real.logb 2 n)) ^ 2) /
      Real.sqrt (Real.logb 2 n) by ring_nf]
  apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < sparsifySchedule n)
    (Real.sqrt_pos.2 hl0)).2
  have := mul_le_mul_of_nonneg_left hroot' (Nat.cast_nonneg n)
  nlinarith

theorem sparsifySchedule_tendsto :
    Filter.Tendsto sparsifySchedule Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro a
  have hc : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have he : 0 < Real.log (2 : ℝ) ^ 4 / (16 * ((a : ℝ) + 1) ^ 2) := by positivity
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 4)).bound he
  have ht : Filter.Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ))
      Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [ht.eventually hsmall, Filter.eventually_ge_atTop (20 : ℕ)] with n hb hn
  have hl := four_le_logb hn
  have hl0 : 0 ≤ Real.logb 2 n := by linarith
  have hlog0 : 0 ≤ Real.log (Real.logb 2 n) := Real.log_nonneg (by linarith)
  have hb' : Real.log (Real.logb 2 n) ^ 4 ≤
      Real.log (2 : ℝ) ^ 4 / (16 * ((a : ℝ) + 1) ^ 2) * Real.logb 2 n := by
    simpa only [Function.id_def, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlog0 4), abs_of_nonneg hl0] using hb
  have hnu := sparsifyNu_le hn
  have hnu4 := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (sparsifyNu n)) hnu 4
  have heq : (2 * Real.logb 2 (Real.logb 2 n)) ^ 4 =
      16 * Real.log (Real.logb 2 n) ^ 4 / Real.log (2 : ℝ) ^ 4 := by
    unfold Real.logb
    ring_nf
  rw [heq] at hnu4
  have hmul : 16 * ((a : ℝ) + 1) ^ 2 * Real.log (Real.logb 2 n) ^ 4 ≤
      Real.log (2 : ℝ) ^ 4 * Real.logb 2 n := by
    have := (le_div_iff₀ (by positivity :
      0 < 16 * ((a : ℝ) + 1) ^ 2)).mp
      (show Real.log (Real.logb 2 n) ^ 4 ≤
        (Real.log (2 : ℝ) ^ 4 * Real.logb 2 n) /
          (16 * ((a : ℝ) + 1) ^ 2) by convert hb' using 1; ring_nf)
    nlinarith
  have ha : (a : ℝ) ^ 2 * (sparsifyNu n : ℝ) ^ 4 ≤ Real.logb 2 n := by
    apply (mul_le_mul_iff_right₀ (pow_pos hc 4)).mp
    have hp := mul_le_mul_of_nonneg_left
      ((le_div_iff₀ (pow_pos hc 4)).mp hnu4) (sq_nonneg (a : ℝ))
    have haa : (a : ℝ) ^ 2 ≤ ((a : ℝ) + 1) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) a]
    nlinarith [mul_le_mul_of_nonneg_right haa
      (pow_nonneg hlog0 4)]
  apply (le_sparsifySchedule_iff hn a).2
  exact_mod_cast ha.trans (sparsifyLambda_bounds hn).1

theorem rho_nonneg (n : ℕ) : 0 ≤ rho n := by
  unfold rho
  positivity

theorem runtimeScale_le_four_rho {n : ℕ} (hn : 20 ≤ n) :
    SqrtLog.Statement.runtimeScale n ≤ 4 * rho n := by
  let c : ℝ := Real.log 2
  let l : ℝ := Real.logb 2 n
  let v : ℝ := Real.logb 2 l
  let y : ℝ := Real.log ((n : ℝ) + 16)
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hc1 : c ≤ 1 := by
    simpa [c] using (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) |>.trans (by norm_num))
  have hl : 4 ≤ l := four_le_logb hn
  have hl0 : 0 < l := by linarith
  have hv : 2 ≤ v := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hl0).mpr
    norm_num
    exact hl
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast (show 16 ≤ n by omega)
  have hcl : c * l = Real.log n := by dsimp [c, l, Real.logb]; field_simp
  have hcv : c * v = Real.log l := by dsimp [c, v, Real.logb]; field_simp
  have hyl : c * l ≤ y := by
    rw [hcl]
    exact Real.log_le_log hn0 (by linarith)
  have hyu : y ≤ 2 * l := by
    have hm : y ≤ Real.log ((2 : ℝ) * n) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne', ← hcl] at hm
    change y ≤ c + c * l at hm
    nlinarith
  have hlogy : Real.log y ≤ 2 * c * v := by
    have h : Real.log y ≤ Real.log (2 * l) :=
      Real.log_le_log (SqrtLog.Statement.log_shift_pos n) hyu
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hl0.ne', ← hcv] at h
    change Real.log y ≤ c + c * v at h
    nlinarith
  have hlogy0 : 0 ≤ Real.log y := (SqrtLog.Statement.log_log_shift_pos n).le
  have hroot : c * Real.sqrt l ≤ Real.sqrt y := by
    apply (Real.le_sqrt (by positivity) (SqrtLog.Statement.log_shift_pos n).le).2
    rw [mul_pow, Real.sq_sqrt hl0.le]
    have hcc : c ^ 2 ≤ c := by nlinarith
    exact (mul_le_mul_of_nonneg_right hcc hl0.le).trans hyl
  have hden : 0 < c * Real.sqrt l := mul_pos hc (Real.sqrt_pos.2 hl0)
  have hsq : Real.log y ^ 2 ≤ (2 * c * v) ^ 2 :=
    pow_le_pow_left₀ hlogy0 hlogy 2
  change (n : ℝ) * Real.log y ^ 2 / Real.sqrt y ≤
    4 * ((n : ℝ) * v ^ 2 / Real.sqrt l)
  calc
    (n : ℝ) * Real.log y ^ 2 / Real.sqrt y ≤
        (n : ℝ) * (2 * c * v) ^ 2 / (c * Real.sqrt l) := by gcongr
    _ = 4 * c * ((n : ℝ) * v ^ 2 / Real.sqrt l) := by
      field_simp
      ring_nf
    _ ≤ 4 * ((n : ℝ) * v ^ 2 / Real.sqrt l) :=
      mul_le_mul_of_nonneg_right (by nlinarith : 4 * c ≤ 4) (by positivity)

theorem rho_le_thirtyTwo_runtimeScale {n : ℕ} (hn : 20 ≤ n) :
    rho n ≤ 32 * SqrtLog.Statement.runtimeScale n := by
  let c : ℝ := Real.log 2
  let l : ℝ := Real.logb 2 n
  let v : ℝ := Real.logb 2 l
  let y : ℝ := Real.log ((n : ℝ) + 16)
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hc1 : c ≤ 1 := by
    simpa [c] using (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      |>.trans (by norm_num))
  have hc2 : (1 : ℝ) / 2 ≤ c := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this
    dsimp [c]
    linarith
  have hl : 4 ≤ l := four_le_logb hn
  have hl0 : 0 < l := by linarith
  have hy0 : 0 < y := SqrtLog.Statement.log_shift_pos n
  have hy2 : 2 ≤ y := SqrtLog.Statement.two_le_log_shift n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast (show 16 ≤ n by omega)
  have hcl : c * l = Real.log n := by dsimp [c, l, Real.logb]; field_simp
  have hcv : c * v = Real.log l := by dsimp [c, v, Real.logb]; field_simp
  have hyl : c * l ≤ y := by
    rw [hcl]
    exact Real.log_le_log hn0 (by linarith)
  have hly : l ≤ 2 * y := by nlinarith
  have hyu : y ≤ 2 * l := by
    have hm : y ≤ Real.log ((2 : ℝ) * n) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne', ← hcl] at hm
    change y ≤ c + c * l at hm
    nlinarith
  have hlogyc : c ≤ Real.log y := Real.log_le_log (by norm_num) hy2
  have hlogy0 : 0 ≤ Real.log y := (SqrtLog.Statement.log_log_shift_pos n).le
  have hv : 0 ≤ v := Real.logb_nonneg (by norm_num) (by linarith)
  have hvu : v ≤ 4 * Real.log y := by
    have h : Real.log l ≤ Real.log (2 * y) := Real.log_le_log hl0 hly
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hy0.ne', ← hcv] at h
    change c * v ≤ c + Real.log y at h
    nlinarith
  have hroot : Real.sqrt y ≤ 2 * Real.sqrt l := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hl0.le]
    nlinarith
  have hvsq : v ^ 2 ≤ 16 * Real.log y ^ 2 := by nlinarith
  change (n : ℝ) * v ^ 2 / Real.sqrt l ≤
    32 * ((n : ℝ) * Real.log y ^ 2 / Real.sqrt y)
  rw [show 32 * ((n : ℝ) * Real.log y ^ 2 / Real.sqrt y) =
    (32 * (n : ℝ) * Real.log y ^ 2) / Real.sqrt y by ring_nf]
  apply (div_le_div_iff₀ (Real.sqrt_pos.2 hl0) (Real.sqrt_pos.2 hy0)).2
  calc
    (n : ℝ) * v ^ 2 * Real.sqrt y ≤
        (n : ℝ) * (16 * Real.log y ^ 2) * (2 * Real.sqrt l) := by gcongr
    _ = _ := by ring_nf

theorem inverse_sparsifySchedule_target {n : ℕ} (hn : 20 ≤ n)
    (hs : 1 ≤ sparsifySchedule n) :
    (n : ℝ) / sparsifySchedule n ≤ 256 * SqrtLog.Statement.runtimeScale n := by
  have := inverse_sparsifySchedule_le hn hs
  have := rho_le_thirtyTwo_runtimeScale hn
  linarith

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
