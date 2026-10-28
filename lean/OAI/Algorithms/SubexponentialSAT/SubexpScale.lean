import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpComputation

namespace OAI.Algorithms

/-!
# Monotonicity of the subexponential scale

Discarding unused variables must not increase the claimed time bound.  This
module proves that fact for the manuscript's exact shifted iterated logarithm.
-/

namespace SubexponentialSAT.SubexpComputation

private theorem concaveOn_logb_two :
    ConcaveOn ℝ (Set.Ioi 0) (Real.logb 2) := by
  let h := ConcaveOn.smul (c := (Real.log 2)⁻¹) (by positivity)
    (StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi)
  change ConcaveOn ℝ (Set.Ioi 0) (fun x => (Real.log 2)⁻¹ * Real.log x) at h
  change ConcaveOn ℝ (Set.Ioi 0) (fun x => Real.log x / Real.log 2)
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- The shift by sixteen makes the logarithm positive even at zero.  Jensen's
inequality applied twice shows that its growth is at most proportional. -/
theorem scaled_logLog_le {m n : ℕ} (hmn : m ≤ n) (hn : 0 < n) :
    ((m : ℝ) / n) * logLog n ≤ logLog m := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmn' : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  let t : ℝ := (m : ℝ) / n
  have ht0 : 0 ≤ t := div_nonneg (Nat.cast_nonneg m) hn'.le
  have ht1 : t ≤ 1 := (div_le_one hn').mpr hmn'
  have ha : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hab : (1 - t) + t = 1 := by ring
  have hblend : (1 - t) * 16 + t * ((n : ℝ) + 16) = (m : ℝ) + 16 := by
    dsimp [t]
    field_simp
    ring
  have hfirst := concaveOn_logb_two.2 (x := 16) (by norm_num)
    (y := (n : ℝ) + 16) (by change 0 < (n : ℝ) + 16; positivity) ha ht0 hab
  simp only [smul_eq_mul, hblend] at hfirst
  have hzero : (0 : ℝ) < Real.logb 2 16 := Real.logb_pos (by norm_num) (by norm_num)
  have hinner := Real.logb_le_logb_of_le (b := 2) (by norm_num)
    (x := 16) (by norm_num) (y := (n : ℝ) + 16)
    (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hblendpos : 0 < (1 - t) * Real.logb 2 16 +
      t * Real.logb 2 ((n : ℝ) + 16) := by
    calc
      0 < Real.logb 2 16 := hzero
      _ = (1 - t) * Real.logb 2 16 + t * Real.logb 2 16 := by ring
      _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left hinner ht0) _
  have hsecond := concaveOn_logb_two.2 (x := Real.logb 2 16) hzero
    (y := Real.logb 2 ((n : ℝ) + 16)) (lt_of_lt_of_le hzero hinner) ha ht0 hab
  simp only [smul_eq_mul] at hsecond
  have hmono := Real.logb_le_logb_of_le (b := 2) (by norm_num) hblendpos hfirst
  have hcombined : (1 - t) * logLog 0 + t * logLog n ≤ logLog m := by
    simpa [logLog] using hsecond.trans hmono
  have hbase : 0 ≤ (1 - t) * logLog 0 := mul_nonneg ha (logLog_pos 0).le
  exact (le_add_of_nonneg_left hbase).trans hcombined

/-- Removing variables preserves the exact exponential envelope. -/
theorem scale_monotone : Monotone scale := by
  intro m n hmn
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
    simp [hm]
  · have h := scaled_logLog_le hmn hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hcross : (m : ℝ) * logLog n ≤ (n : ℝ) * logLog m := by
      have hdiv : ((m : ℝ) * logLog n) / n ≤ logLog m := by
        simpa [div_mul_eq_mul_div] using h
      have hc := (div_le_iff₀ hn').mp hdiv
      simpa [mul_comm] using hc
    exact (div_le_div_iff₀ (logLog_pos m) (logLog_pos n)).mpr hcross

theorem runtimeBound_mono_variables {constant exponentConstant : ℝ}
    (hc : 0 ≤ constant) (ha : 0 ≤ exponentConstant) (degree inputBits : ℕ)
    {m n : ℕ} (hmn : m ≤ n) :
    runtimeBound constant exponentConstant degree inputBits m ≤
      runtimeBound constant exponentConstant degree inputBits n := by
  apply mul_le_mul_of_nonneg_left
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (scale_monotone hmn) ha)
  · exact mul_nonneg hc (pow_nonneg (by positivity) degree)

end SubexponentialSAT.SubexpComputation

end OAI.Algorithms
