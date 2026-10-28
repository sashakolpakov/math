import OAI.Analysis.PDE.Concentration.EscapeBarrier

namespace OAI.Analysis.PDE.Concentration

/-- Clearing the two positive logarithmic propagation factors gives a
quadratic logarithmic loss, uniformly in the inner radius. -/
theorem logarithmic_factors_upper {ρ D H v : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hD : 0 ≤ D) (hv : 0 ≤ v)
    (h : H * (Real.log 3 / (4 * (Real.log 3 - Real.log ρ))) *
      (Real.log 2 / (2 * (-Real.log ρ))) ≤ D * v) :
    H ≤ (8 * D / (Real.log 3 * Real.log 2)) * (Real.log 3 - Real.log ρ) ^ 2 * v := by
  have hp : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hr : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 < -Real.log ρ := neg_pos.mpr (Real.log_neg hρ hρ1)
  have hL : 0 < Real.log 3 - Real.log ρ := by linarith
  have hden : 0 < 8 * (Real.log 3 - Real.log ρ) * (-Real.log ρ) := by positivity
  have he : H * (Real.log 3 / (4 * (Real.log 3 - Real.log ρ))) *
      (Real.log 2 / (2 * (-Real.log ρ))) =
      (H * (Real.log 3 * Real.log 2)) /
        (8 * (Real.log 3 - Real.log ρ) * (-Real.log ρ)) := by
    field_simp
    ring
  rw [he] at h
  have hh := (div_le_iff₀ hden).mp h
  have hs : 8 * (Real.log 3 - Real.log ρ) * (-Real.log ρ) ≤
      8 * (Real.log 3 - Real.log ρ) ^ 2 := by nlinarith
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hs (mul_nonneg hD hv))
  have hfinal := (le_div_iff₀ (mul_pos hp hr)).mpr hh'
  convert hfinal using 1 ; ring

theorem logarithmic_factors_cubic_upper {ρ D H v : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hD : 0 ≤ D) (hv : 0 ≤ v)
    (h : H * (Real.log 3 / (4 * (Real.log 3 - Real.log ρ))) *
      (Real.log 2 / (2 * (-Real.log ρ))) ≤ D * v) :
    H ≤ (8 * D / (Real.log 3 * Real.log 2) * (Real.log 3 + 1) ^ 2) *
      (1 + |Real.log ρ|) ^ 3 * v := by
  have hp : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hr : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 < -Real.log ρ := neg_pos.mpr (Real.log_neg hρ hρ1)
  have hL : 0 ≤ Real.log 3 - Real.log ρ := by linarith
  have habs : |Real.log ρ| = -Real.log ρ := abs_of_neg (Real.log_neg hρ hρ1)
  have hbase : Real.log 3 - Real.log ρ ≤ (Real.log 3 + 1) * (1 + |Real.log ρ|) := by
    rw [habs]
    nlinarith [mul_nonneg hp.le hq.le]
  have hs := pow_le_pow_left₀ hL hbase 2
  have hcub : (1 + |Real.log ρ|) ^ 2 ≤ (1 + |Real.log ρ|) ^ 3 := by
    nlinarith [sq_nonneg (1 + |Real.log ρ|), abs_nonneg (Real.log ρ),
      mul_nonneg (sq_nonneg (1 + |Real.log ρ|)) (abs_nonneg (Real.log ρ))]
  have hs' : (Real.log 3 - Real.log ρ) ^ 2 ≤
      (Real.log 3 + 1) ^ 2 * (1 + |Real.log ρ|) ^ 3 := by
    rw [mul_pow] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left hcub (sq_nonneg _))
  have hc : 0 ≤ 8 * D / (Real.log 3 * Real.log 2) := by positivity
  exact (logarithmic_factors_upper hρ hρ1 hD hv h).trans (by
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs' hc) hv])

end OAI.Analysis.PDE.Concentration
