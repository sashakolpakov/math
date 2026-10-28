import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Growing-parameter exponent arithmetic

All factors in this module are actual real powers. The bounds expose the
growing parameters; they assert no program-running-time fact.
-/

namespace SubexponentialSAT.SubexpExponentArithmetic

noncomputable section
open Filter
open scoped Topology

/-- The real logarithmic scale used in the final statement. -/
def shiftedLogLog (n : ℝ) : ℝ := Real.logb 2 (Real.logb 2 (n + 16))

def scale (n : ℝ) : ℝ := n / shiftedLogLog n

/-- The exponential part of one leaf calculation, with its overhead constant visible. -/
def exponentialPart (p alpha c D : ℝ) : ℝ :=
  p ^ (alpha * D) * (2 : ℝ) ^ (c * D)

theorem alpha_le_three_div (r : ℝ) :
    1 - (1 - 1 / r) ^ 2 + 1 / r ≤ 3 / r := by
  simp only [div_eq_mul_inv]
  nlinarith [sq_nonneg r⁻¹]

theorem log_two_pos : 0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)

theorem exponentialPart_eq {p : ℝ} (hp : 0 < p) (alpha c D : ℝ) :
    exponentialPart p alpha c D =
      (2 : ℝ) ^ ((alpha * Real.logb 2 p + c) * D) := by
  unfold exponentialPart Real.logb
  rw [Real.rpow_def_of_pos hp,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
  congr 1
  field_simp

/-- The packing ceiling gives D ≤ 33 n/s for the source's bit capacity range. -/
theorem dimension_le {n s ell D : ℝ}
    (hs : 32 ≤ s) (hsn : s ≤ n)
    (helllo : s / 32 ≤ ell) (hD : D ≤ n / ell + 1) :
    D ≤ 33 * (n / s) := by
  have hspos : 0 < s := by linarith
  have hellpos : 0 < ell := by linarith
  have hn : 0 ≤ n := by linarith
  have hratio : 1 ≤ n / s := (le_div_iff₀ hspos).2 (by simpa using hsn)
  have hmul : s * (n / s) = n := by field_simp
  have hscale := mul_le_mul_of_nonneg_right helllo (div_nonneg hn hspos.le)
  have hdiv : n / ell ≤ 32 * (n / s) := by
    apply (div_le_iff₀ hellpos).2
    nlinarith
  linarith

/-- Explicit Section 5.4 bound, before raising two to these exponents. -/
theorem exponent_le {p n s ell D alpha c : ℝ}
    (hp : 1 ≤ p) (hs : 32 ≤ s) (hsn : s ≤ n)
    (helllo : s / 32 ≤ ell) (hellhi : ell ≤ s)
    (hD0 : 0 ≤ D) (hD : D ≤ n / ell + 1)
    (hlog : Real.logb 2 p ≤ ell + 1)
    (halpha : alpha ≤ 3 / s) (hc : 0 ≤ c) :
    (alpha * Real.logb 2 p + c) * D ≤ (12 + 33 * c) * (n / s) := by
  have hspos : 0 < s := by linarith
  have hellone : 1 ≤ ell := by linarith
  have hellpos : 0 < ell := by linarith
  have hn : 0 ≤ n := by linarith
  have hlog0 : 0 ≤ Real.logb 2 p := Real.logb_nonneg (by norm_num) hp
  have hDsub : D - 1 ≤ n / ell := by linarith
  have hDmul := (le_div_iff₀ hellpos).mp hDsub
  have hpair : (ell + 1) * D ≤ 4 * n := by
    nlinarith
  have hfirst : alpha * Real.logb 2 p ≤ (3 / s) * (ell + 1) :=
    (mul_le_mul_of_nonneg_right halpha hlog0).trans
      (mul_le_mul_of_nonneg_left hlog (by positivity))
  have hfirstD := mul_le_mul_of_nonneg_right hfirst hD0
  have hpairScaled := mul_le_mul_of_nonneg_left hpair
    (by positivity : 0 ≤ (3 : ℝ) / s)
  have hfield : alpha * Real.logb 2 p * D ≤ 12 * (n / s) := by
    calc
      alpha * Real.logb 2 p * D ≤ (3 / s) * (ell + 1) * D := hfirstD
      _ = (3 / s) * ((ell + 1) * D) := by ring
      _ ≤ (3 / s) * (4 * n) := hpairScaled
      _ = 12 * (n / s) := by ring
  have hsymbolic := mul_le_mul_of_nonneg_left
    (dimension_le hs hsn helllo hD) hc
  nlinarith

/-- No input-dependent multiplicative constant is hidden in this inequality. -/
theorem exponentialPart_le {p n s ell D alpha c : ℝ}
    (hp : 1 ≤ p) (hs : 32 ≤ s) (hsn : s ≤ n)
    (helllo : s / 32 ≤ ell) (hellhi : ell ≤ s)
    (hD0 : 0 ≤ D) (hD : D ≤ n / ell + 1)
    (hlog : Real.logb 2 p ≤ ell + 1)
    (halpha : alpha ≤ 3 / s) (hc : 0 ≤ c) :
    exponentialPart p alpha c D ≤
      (2 : ℝ) ^ ((12 + 33 * c) * (n / s)) := by
  rw [exponentialPart_eq (lt_of_lt_of_le (by norm_num) hp)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (exponent_le hp hs hsn helllo hellhi hD0 hD hlog halpha hc)

/-- A polynomial base can be rewritten as an actual base-two real power. -/
theorem rpow_eq_two_rpow_logb {x : ℝ} (hx : 0 < x) (d : ℝ) :
    x ^ d = (2 : ℝ) ^ (d * Real.logb 2 x) := by
  rw [Real.rpow_def_of_pos hx,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  unfold Real.logb
  field_simp

theorem shiftedLogLog_pos {n : ℝ} (hn : 0 ≤ n) : 0 < shiftedLogLog n := by
  unfold shiftedLogLog
  apply Real.logb_pos (by norm_num)
  apply (Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2)
    (by linarith : 0 < n + 16)).2
  norm_num
  linarith

/-- The square of log base two is eventually at most n, with the shift included. -/
theorem eventually_logb_sq_le :
    ∀ᶠ n : ℝ in atTop, (Real.logb 2 (n + 16)) ^ 2 ≤ n := by
  have ht : Tendsto (fun n : ℝ => n + 16) atTop atTop :=
    tendsto_id.atTop_add tendsto_const_nhds
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound
    (show 0 < (Real.log (2 : ℝ)) ^ 2 / 2 by positivity)
  filter_upwards [ht.eventually hsmall, eventually_ge_atTop (16 : ℝ)] with n hb hn
  have hnp : 0 ≤ n + 16 := by linarith
  have hb' : (Real.log (n + 16)) ^ 2 ≤
      (Real.log (2 : ℝ)) ^ 2 / 2 * (n + 16) := by
    simpa only [Function.id_def, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (Real.log (n + 16))),
      abs_of_nonneg hnp] using hb
  calc
    (Real.logb 2 (n + 16)) ^ 2 =
        (Real.log (n + 16)) ^ 2 / (Real.log (2 : ℝ)) ^ 2 := by
      unfold Real.logb
      ring
    _ ≤ (n + 16) / 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos log_two_pos)).2
      nlinarith
    _ ≤ n := by linarith

/-- The iterated logarithm is eventually bounded by the first logarithm. -/
theorem eventually_shiftedLogLog_le_logb :
    ∀ᶠ n : ℝ in atTop, shiftedLogLog n ≤ Real.logb 2 (n + 16) := by
  have ht : Tendsto (fun n : ℝ => Real.logb 2 (n + 16)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_id.atTop_add tendsto_const_nhds)
  have hsmall := Real.isLittleO_log_id_atTop.bound log_two_pos
  filter_upwards [ht.eventually hsmall, eventually_ge_atTop (0 : ℝ)] with n hb hn
  have ht0 : 0 ≤ Real.logb 2 (n + 16) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hb' : Real.log (Real.logb 2 (n + 16)) ≤
      Real.log 2 * Real.logb 2 (n + 16) := by
    calc
      Real.log (Real.logb 2 (n + 16)) ≤
          |Real.log (Real.logb 2 (n + 16))| := le_abs_self _
      _ ≤ Real.log 2 * Real.logb 2 (n + 16) := by
        simpa only [Function.id_def, Real.norm_eq_abs, abs_of_nonneg ht0] using hb
  exact (div_le_iff₀ log_two_pos).2 (by
    simpa only [mul_comm] using hb')

/-- The polynomial-overhead absorption inequality is proved from logarithm
growth, rather than supplied as a runtime assumption. -/
theorem eventually_logb_le_scale :
    ∀ᶠ n : ℝ in atTop, Real.logb 2 (n + 16) ≤ scale n := by
  filter_upwards [eventually_logb_sq_le, eventually_shiftedLogLog_le_logb,
    eventually_ge_atTop (0 : ℝ)] with n hsq hiter hn
  have ht0 : 0 ≤ Real.logb 2 (n + 16) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hiter ht0
  exact (le_div_iff₀ (shiftedLogLog_pos hn)).2 (by nlinarith)

theorem eventually_logb_le_scale_nat :
    ∀ᶠ n : ℕ in atTop, Real.logb 2 ((n : ℝ) + 16) ≤ scale (n : ℝ) :=
  (tendsto_natCast_atTop_atTop (R := ℝ)).eventually eventually_logb_le_scale

theorem logb_lt_natLog2_add_one (n : ℕ) :
    Real.logb 2 (n : ℝ) < (Nat.log2 n : ℝ) + 1 := by
  have hf : ⌊Real.logb 2 (n : ℝ)⌋₊ = Nat.log2 n := by
    rw [Nat.log2_eq_log_two]
    exact Real.natFloor_logb_natCast 2 n
  simpa only [hf] using
    (Nat.lt_floor_add_one (Real.logb 2 (n : ℝ)))

/-- Lower comparison needed for the growing per-node search exponent. -/
theorem natLog2_le_shiftedLogLog {n : ℕ} (hn : 2 ≤ n) :
    (Nat.log2 (Nat.log2 n) : ℝ) ≤ shiftedLogLog (n : ℝ) := by
  have hm : 1 ≤ Nat.log2 n := by
    rw [Nat.log2_eq_log_two]
    exact Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
  have hmreal : (1 : ℝ) ≤ Nat.log2 n := by exact_mod_cast hm
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hinner : (Nat.log2 n : ℝ) ≤ Real.logb 2 ((n : ℝ) + 16) := by
    calc
      (Nat.log2 n : ℝ) ≤ Real.logb 2 (n : ℝ) := by
        simpa [Nat.log2_eq_log_two] using (Real.natLog_le_logb n 2)
      _ ≤ Real.logb 2 ((n : ℝ) + 16) :=
        Real.logb_le_logb_of_le (by norm_num) hnp (by linarith)
  calc
    (Nat.log2 (Nat.log2 n) : ℝ) ≤ Real.logb 2 (Nat.log2 n : ℝ) := by
      simpa [Nat.log2_eq_log_two] using (Real.natLog_le_logb (Nat.log2 n) 2)
    _ ≤ shiftedLogLog (n : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) hinner

/-- The two integer logarithms lose at most a constant factor on the final scale. -/
theorem shiftedLogLog_le_twice_natLog2 {n : ℕ} (hn : 16 ≤ n) :
    shiftedLogLog (n : ℝ) ≤ 2 * (Nat.log2 (Nat.log2 n) : ℝ) := by
  have hnreal : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  have hm : 4 ≤ Nat.log2 n := by
    rw [Nat.log2_eq_log_two]
    exact Nat.le_log_of_pow_le (by norm_num) (by norm_num; exact hn)
  have hs : 2 ≤ Nat.log2 (Nat.log2 n) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.le_log_of_pow_le (by norm_num) (by norm_num; exact hm)
  have hmreal : (4 : ℝ) ≤ Nat.log2 n := by exact_mod_cast hm
  have hsreal : (2 : ℝ) ≤ Nat.log2 (Nat.log2 n) := by exact_mod_cast hs
  have hmpos : (0 : ℝ) < Nat.log2 n := by linarith
  have hshift : Real.logb 2 ((n : ℝ) + 16) ≤ 1 + Real.logb 2 (n : ℝ) := by
    calc
      Real.logb 2 ((n : ℝ) + 16) ≤ Real.logb 2 (2 * (n : ℝ)) :=
        Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
      _ = 1 + Real.logb 2 (n : ℝ) := by
        rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) hnp.ne']
        norm_num
  have ht : Real.logb 2 ((n : ℝ) + 16) < 2 * (Nat.log2 n : ℝ) := by
    have h := logb_lt_natLog2_add_one n
    linarith
  have htpos : 0 < Real.logb 2 ((n : ℝ) + 16) :=
    Real.logb_pos (by norm_num) (by linarith)
  calc
    shiftedLogLog (n : ℝ) ≤ Real.logb 2 (2 * (Nat.log2 n : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) htpos ht.le
    _ = 1 + Real.logb 2 (Nat.log2 n : ℝ) := by
      rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) hmpos.ne']
      norm_num
    _ ≤ 2 * (Nat.log2 (Nat.log2 n) : ℝ) := by
      have h := logb_lt_natLog2_add_one (Nat.log2 n)
      linarith

theorem natLog2_ratio_le_twice_scale {n : ℕ} (hn : 16 ≤ n) :
    (n : ℝ) / (Nat.log2 (Nat.log2 n) : ℝ) ≤ 2 * scale (n : ℝ) := by
  have hcomp := shiftedLogLog_le_twice_natLog2 hn
  have hS := shiftedLogLog_pos (Nat.cast_nonneg n)
  have hs : 0 < (Nat.log2 (Nat.log2 n) : ℝ) := by linarith
  unfold scale
  rw [show 2 * ((n : ℝ) / shiftedLogLog (n : ℝ)) =
    (2 * (n : ℝ)) / shiftedLogLog (n : ℝ) by ring]
  apply (div_le_div_iff₀ hs hS).2
  have hmul := mul_le_mul_of_nonneg_left hcomp (Nat.cast_nonneg n)
  nlinarith

theorem polynomial_factor_le {n d : ℝ} (hn : 0 ≤ n) (hd : 0 ≤ d)
    (hlog : Real.logb 2 (n + 16) ≤ scale n) :
    (n + 16) ^ d ≤ (2 : ℝ) ^ (d * scale n) := by
  rw [rpow_eq_two_rpow_logb (by linarith : 0 < n + 16)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (mul_le_mul_of_nonneg_left hlog hd)

/-- All polynomial overhead is represented by H ≤ (n+16)^d with d explicit.
The extra color factor r is also charged, rather than hidden in a constant. -/
theorem parameter_cost_le {p n s ell D alpha c d r H : ℝ}
    (hp : 1 ≤ p) (hs : 32 ≤ s) (hsn : s ≤ n)
    (helllo : s / 32 ≤ ell) (hellhi : ell ≤ s)
    (hD0 : 0 ≤ D) (hD : D ≤ n / ell + 1)
    (hlog : Real.logb 2 p ≤ ell + 1)
    (halpha : alpha ≤ 3 / s) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hr0 : 0 ≤ r) (hr : r ≤ n + 16)
    (hH : H ≤ (n + 16) ^ d)
    (hratio : n / s ≤ 2 * scale n)
    (hlogn : Real.logb 2 (n + 16) ≤ scale n) :
    H * r * exponentialPart p alpha c D ≤
      (2 : ℝ) ^ ((2 * (12 + 33 * c) + d + 1) * scale n) := by
  have hn : 0 ≤ n := by linarith
  have hbase : 0 < n + 16 := by linarith
  have hK : 0 ≤ 12 + 33 * c := by linarith
  have hExp0 : 0 ≤ exponentialPart p alpha c D := by
    unfold exponentialPart
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by norm_num) _)
  have hHr : H * r ≤ (n + 16) ^ (d + 1) := by
    calc
      H * r ≤ (n + 16) ^ d * (n + 16) :=
        mul_le_mul hH hr hr0 (Real.rpow_nonneg hbase.le _)
      _ = (n + 16) ^ (d + 1) := (Real.rpow_add_one hbase.ne' d).symm
  have hExp : exponentialPart p alpha c D ≤
      (2 : ℝ) ^ ((2 * (12 + 33 * c)) * scale n) := by
    refine (exponentialPart_le hp hs hsn helllo hellhi hD0 hD hlog halpha hc).trans ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h := mul_le_mul_of_nonneg_left hratio hK
    nlinarith
  calc
    H * r * exponentialPart p alpha c D ≤
        (n + 16) ^ (d + 1) *
          (2 : ℝ) ^ ((2 * (12 + 33 * c)) * scale n) :=
      mul_le_mul hHr hExp hExp0 (Real.rpow_nonneg hbase.le _)
    _ ≤ (2 : ℝ) ^ ((d + 1) * scale n) *
          (2 : ℝ) ^ ((2 * (12 + 33 * c)) * scale n) :=
      mul_le_mul_of_nonneg_right (polynomial_factor_le hn (by linarith) hlogn)
        (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ ((2 * (12 + 33 * c) + d + 1) * scale n) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

/-- Also charge the sparsification factor 2^(n/s). -/
theorem branched_parameter_cost_le {p n s ell D alpha c d r H : ℝ}
    (hp : 1 ≤ p) (hs : 32 ≤ s) (hsn : s ≤ n)
    (helllo : s / 32 ≤ ell) (hellhi : ell ≤ s)
    (hD0 : 0 ≤ D) (hD : D ≤ n / ell + 1)
    (hlog : Real.logb 2 p ≤ ell + 1)
    (halpha : alpha ≤ 3 / s) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hr0 : 0 ≤ r) (hr : r ≤ n + 16)
    (hH : H ≤ (n + 16) ^ d)
    (hratio : n / s ≤ 2 * scale n)
    (hlogn : Real.logb 2 (n + 16) ≤ scale n) :
    (2 : ℝ) ^ (n / s) * (H * r * exponentialPart p alpha c D) ≤
      (2 : ℝ) ^ ((27 + 66 * c + d) * scale n) := by
  have hcost := parameter_cost_le hp hs hsn helllo hellhi hD0 hD hlog halpha hc
    hd hr0 hr hH hratio hlogn
  calc
    (2 : ℝ) ^ (n / s) * (H * r * exponentialPart p alpha c D) ≤
        (2 : ℝ) ^ (n / s) *
          (2 : ℝ) ^ ((2 * (12 + 33 * c) + d + 1) * scale n) :=
      mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg (by norm_num) _)
    _ ≤ (2 : ℝ) ^ (2 * scale n) *
          (2 : ℝ) ^ ((2 * (12 + 33 * c) + d + 1) * scale n) :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hratio)
        (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ ((27 + 66 * c + d) * scale n) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

/-- For the source's actual integer s, the analytical scale assumptions are
discharged eventually. Remaining hypotheses concern the concrete parameters. -/
theorem eventually_branched_parameter_cost_le :
    ∀ᶠ n : ℕ in atTop, ∀ p ell D alpha c d r H : ℝ,
      1 ≤ p →
      32 ≤ (Nat.log2 (Nat.log2 n) : ℝ) →
      (Nat.log2 (Nat.log2 n) : ℝ) / 32 ≤ ell →
      ell ≤ (Nat.log2 (Nat.log2 n) : ℝ) →
      0 ≤ D →
      D ≤ (n : ℝ) / ell + 1 →
      Real.logb 2 p ≤ ell + 1 →
      alpha ≤ 3 / (Nat.log2 (Nat.log2 n) : ℝ) →
      0 ≤ c → 0 ≤ d → 0 ≤ r → r ≤ (n : ℝ) + 16 →
      H ≤ ((n : ℝ) + 16) ^ d →
      (2 : ℝ) ^ ((n : ℝ) / (Nat.log2 (Nat.log2 n) : ℝ)) *
          (H * r * exponentialPart p alpha c D) ≤
        (2 : ℝ) ^ ((27 + 66 * c + d) * scale (n : ℝ)) := by
  filter_upwards [eventually_logb_le_scale_nat, eventually_ge_atTop (16 : ℕ)] with n hlogn hn
  intro p ell D alpha c d r H hp hs helllo hellhi hD0 hD hlog halpha hc hd hr0 hr hH
  apply branched_parameter_cost_le hp hs _ helllo hellhi hD0 hD hlog halpha hc
    hd hr0 hr hH (natLog2_ratio_le_twice_scale hn) hlogn
  have hnat : Nat.log2 (Nat.log2 n) ≤ n := by
    simp only [Nat.log2_eq_log_two]
    exact (Nat.log_le_self 2 (Nat.log 2 n)).trans (Nat.log_le_self 2 n)
  exact_mod_cast hnat

/-- The source's choices tau = 1/s, r = s, and c = 128, with a completely
explicit final coefficient. No field-size or layout constant is held fixed. -/
theorem eventually_source_cost_le :
    ∀ᶠ n : ℕ in atTop,
      let s : ℝ := Nat.log2 (Nat.log2 n)
      ∀ p ell D d H : ℝ,
        1 ≤ p → 32 ≤ s → s / 32 ≤ ell → ell ≤ s →
        0 ≤ D → D ≤ (n : ℝ) / ell + 1 →
        Real.logb 2 p ≤ ell + 1 → 0 ≤ d →
        H ≤ ((n : ℝ) + 16) ^ d →
        (2 : ℝ) ^ ((n : ℝ) / s) *
            (H * s * exponentialPart p (1 - (1 - 1 / s) ^ 2 + 1 / s) 128 D) ≤
          (2 : ℝ) ^ ((8475 + d) * scale (n : ℝ)) := by
  filter_upwards [eventually_branched_parameter_cost_le] with n h
  dsimp only
  intro p ell D d H hp hs helllo hellhi hD0 hD hlog hd hH
  have hsn : (Nat.log2 (Nat.log2 n) : ℝ) ≤ n := by
    exact_mod_cast (show Nat.log2 (Nat.log2 n) ≤ n by
      simp only [Nat.log2_eq_log_two]
      exact (Nat.log_le_self 2 (Nat.log 2 n)).trans (Nat.log_le_self 2 n))
  have hf := h p ell D _ 128 d (Nat.log2 (Nat.log2 n)) H hp hs helllo hellhi hD0 hD
    hlog (alpha_le_three_div _) (by norm_num) hd (by linarith) (by linarith) hH
  norm_num only [show (27 : ℝ) + 66 * 128 = 8475 by norm_num] at hf
  exact hf

end
end SubexponentialSAT.SubexpExponentArithmetic

end OAI.Algorithms
