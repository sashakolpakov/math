import OAI.Analysis.Fourier.SquareFunction.Maximal

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem lintegral_power_Ici {b q : ℝ} (hb : 0 < b) (hq : q < -1) :
    (∫⁻ t : ℝ in Ici b, ENNReal.ofReal t ^ q) =
      ENNReal.ofReal (b ^ (q + 1) / (-q - 1)) := by
  rw [← restrict_Ioi_eq_restrict_Ici]
  have hi := integrableOn_Ioi_rpow_of_lt hq hb
  calc
    _ = ∫⁻ t : ℝ in Ioi b, ENNReal.ofReal (t ^ q) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact ENNReal.ofReal_rpow_of_pos (hb.trans ht)
    _ = ENNReal.ofReal (∫ t : ℝ in Ioi b, t ^ q) :=
      (ofReal_integral_eq_lintegral_ofReal hi (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact Real.rpow_nonneg (hb.trans ht).le _)).symm
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt hq hb]
      congr 1
      rw [show -q - 1 = -(q + 1) by ring, div_neg, neg_div]

/-- The low-amplitude term in Marcinkiewicz interpolation, evaluated by
Tonelli. Together with the weighted-tail identity this gives the complete
`L1`/`L2` interpolation estimate. -/
theorem lintegral_weighted_head_square {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ} (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ (2 : ℝ) ∂μ) *
        ENNReal.ofReal t ^ (p - 3)) =
      ENNReal.ofReal (1 / (2 - p)) * ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ := by
  let F : X × ℝ → ℝ≥0∞ := {z | f z.1 ≤ z.2}.indicator
    (fun z ↦ ENNReal.ofReal (f z.1) ^ (2 : ℝ) * ENNReal.ofReal z.2 ^ (p - 3))
  have hF : Measurable F :=
    (((hf.comp measurable_fst).ennreal_ofReal.pow_const (2 : ℝ)).mul
      (measurable_snd.ennreal_ofReal.pow_const (p - 3))).indicator
      (measurableSet_le (hf.comp measurable_fst) measurable_snd)
  have hleft (t : ℝ) : (∫⁻ x, F (x, t) ∂μ) =
      (∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ (2 : ℝ) ∂μ) *
        ENNReal.ofReal t ^ (p - 3) := by
    change (∫⁻ x, {x | f x ≤ t}.indicator
      (fun x ↦ ENNReal.ofReal (f x) ^ (2 : ℝ) * ENNReal.ofReal t ^ (p - 3)) x ∂μ) = _
    rw [lintegral_indicator (measurableSet_le hf measurable_const),
      lintegral_mul_const _ (hf.ennreal_ofReal.pow_const (2 : ℝ))]
  have hright (x : X) : (∫⁻ t in Ioi (0 : ℝ), F (x, t)) =
      ENNReal.ofReal (1 / (2 - p)) * ENNReal.ofReal (f x) ^ p := by
    by_cases hx0 : f x = 0
    · simp [F, Set.indicator_apply, hx0, show 0 < p by linarith]
    have hx : 0 < f x := lt_of_le_of_ne (hfn x) (Ne.symm hx0)
    change (∫⁻ t in Ioi (0 : ℝ), (Ici (f x)).indicator
      (fun t ↦ ENNReal.ofReal (f x) ^ (2 : ℝ) * ENNReal.ofReal t ^ (p - 3)) t) = _
    rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      inter_eq_left.mpr (by intro t ht; exact hx.trans_le ht),
      lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top),
      lintegral_power_Ici hx (by linarith)]
    have hd : 0 < 2 - p := by linarith
    simp only [show p - 3 + 1 = p - 2 by ring, show -(p - 3) - 1 = 2 - p by ring]
    rw [ENNReal.ofReal_div_of_pos hd, ← ENNReal.ofReal_rpow_of_pos hx,
      ENNReal.ofReal_div_of_pos hd, ENNReal.ofReal_one]
    have he : ENNReal.ofReal (f x) ^ (2 : ℝ) * ENNReal.ofReal (f x) ^ (p - 2) =
        ENNReal.ofReal (f x) ^ p := by
      rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_ne_zero_iff.mpr hx) ENNReal.ofReal_ne_top]
      congr 1
      ring
    simp only [div_eq_mul_inv, one_mul]
    rw [← mul_assoc, he, mul_comm]
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, F (x, t) ∂μ := by simp_rw [hleft]
    _ = ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), F (x, t)) ∂μ :=
      (lintegral_lintegral_swap (μ := μ) (ν := volume.restrict (Ioi (0 : ℝ)))
        (f := fun x t ↦ F (x, t)) hF.aemeasurable).symm
    _ = _ := by
      simp_rw [hright]
      exact lintegral_const_mul _ (hf.ennreal_ofReal.pow_const p)

end OAI.Analysis.Fourier.Restriction
