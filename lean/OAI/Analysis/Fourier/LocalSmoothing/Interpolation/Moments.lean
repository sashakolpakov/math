import OAI.Analysis.Fourier.Restriction.WeakInterpolation

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation

/-- Exact weighted tail integral for arbitrary positive endpoint exponent. -/
theorem weighted_tail_power {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ} (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {p q : ℝ} (hq : 0 < q) (hqp : q < p) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q ∂μ) *
        ENNReal.ofReal t ^ (p - q - 1)) =
      ENNReal.ofReal (1 / (p - q)) * ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ := by
  let F : X × ℝ → ℝ≥0∞ := {z | z.2 < f z.1}.indicator
    (fun z => ENNReal.ofReal (f z.1) ^ q * ENNReal.ofReal z.2 ^ (p - q - 1))
  have hF : Measurable F :=
    (((hf.comp measurable_fst).ennreal_ofReal.pow_const q).mul
      (measurable_snd.ennreal_ofReal.pow_const (p - q - 1))).indicator
      (measurableSet_lt measurable_snd (hf.comp measurable_fst))
  have hleft (t : ℝ) : (∫⁻ x, F (x,t) ∂μ) =
      (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q ∂μ) *
        ENNReal.ofReal t ^ (p - q - 1) := by
    change (∫⁻ x, {x | t < f x}.indicator
      (fun x => ENNReal.ofReal (f x) ^ q * ENNReal.ofReal t ^ (p - q - 1)) x ∂μ) = _
    rw [lintegral_indicator (measurableSet_lt measurable_const hf),
      lintegral_mul_const _ (hf.ennreal_ofReal.pow_const q)]
  have hright (x : X) : (∫⁻ t in Ioi (0 : ℝ), F (x,t)) =
      ENNReal.ofReal (1 / (p - q)) * ENNReal.ofReal (f x) ^ p := by
    change (∫⁻ t in Ioi (0 : ℝ), (Iio (f x)).indicator
      (fun t => ENNReal.ofReal (f x) ^ q * ENNReal.ofReal t ^ (p - q - 1)) t) = _
    rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      inter_comm (Iio (f x)), Ioi_inter_Iio,
      lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top),
      OAI.Analysis.Fourier.SquareFunction.lintegral_power_Ioo (hfn x) (by linarith)]
    have hd : 0 < p - q := sub_pos.mpr hqp
    simp only [show p - q - 1 + 1 = p - q by ring]
    rw [ENNReal.ofReal_div_of_pos hd, ← ENNReal.ofReal_rpow_of_nonneg (hfn x) hd.le,
      ENNReal.ofReal_div_of_pos hd, ENNReal.ofReal_one]
    have he : ENNReal.ofReal (f x) ^ q * ENNReal.ofReal (f x) ^ (p - q) =
        ENNReal.ofReal (f x) ^ p := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ hq.le hd.le]
      congr 1
      ring
    simp only [div_eq_mul_inv,one_mul]
    rw [← mul_assoc,he,mul_comm]
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, F (x,t) ∂μ := by simp_rw [hleft]
    _ = ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), F (x,t)) ∂μ :=
      (lintegral_lintegral_swap (μ := μ) (ν := volume.restrict (Ioi (0 : ℝ)))
        (f := fun x t => F (x,t)) hF.aemeasurable).symm
    _ = _ := by
      simp_rw [hright]
      exact lintegral_const_mul _ (hf.ennreal_ofReal.pow_const p)

/-- Exact weighted head integral for arbitrary upper endpoint exponent. -/
theorem weighted_head_power {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ} (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ q ∂μ) *
        ENNReal.ofReal t ^ (p - q - 1)) =
      ENNReal.ofReal (1 / (q - p)) * ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ := by
  let F : X × ℝ → ℝ≥0∞ := {z | f z.1 ≤ z.2}.indicator
    (fun z => ENNReal.ofReal (f z.1) ^ q * ENNReal.ofReal z.2 ^ (p - q - 1))
  have hq : 0 < q := hp.trans hpq
  have hF : Measurable F :=
    (((hf.comp measurable_fst).ennreal_ofReal.pow_const q).mul
      (measurable_snd.ennreal_ofReal.pow_const (p - q - 1))).indicator
      (measurableSet_le (hf.comp measurable_fst) measurable_snd)
  have hleft (t : ℝ) : (∫⁻ x, F (x,t) ∂μ) =
      (∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ q ∂μ) *
        ENNReal.ofReal t ^ (p - q - 1) := by
    change (∫⁻ x, {x | f x ≤ t}.indicator
      (fun x => ENNReal.ofReal (f x) ^ q * ENNReal.ofReal t ^ (p - q - 1)) x ∂μ) = _
    rw [lintegral_indicator (measurableSet_le hf measurable_const),
      lintegral_mul_const _ (hf.ennreal_ofReal.pow_const q)]
  have hright (x : X) : (∫⁻ t in Ioi (0 : ℝ), F (x,t)) =
      ENNReal.ofReal (1 / (q - p)) * ENNReal.ofReal (f x) ^ p := by
    by_cases hx0 : f x = 0
    · simp [F,Set.indicator_apply,hx0,hp,hq]
    have hx : 0 < f x := lt_of_le_of_ne (hfn x) (Ne.symm hx0)
    change (∫⁻ t in Ioi (0 : ℝ), (Ici (f x)).indicator
      (fun t => ENNReal.ofReal (f x) ^ q * ENNReal.ofReal t ^ (p - q - 1)) t) = _
    rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      inter_eq_left.mpr (by intro t ht; exact hx.trans_le ht),
      lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top),
      OAI.Analysis.Fourier.Restriction.lintegral_power_Ici hx (by linarith)]
    have hd : 0 < q - p := sub_pos.mpr hpq
    simp only [show p - q - 1 + 1 = p - q by ring,
      show -(p - q - 1) - 1 = q - p by ring]
    rw [ENNReal.ofReal_div_of_pos hd, ← ENNReal.ofReal_rpow_of_pos hx,
      ENNReal.ofReal_div_of_pos hd, ENNReal.ofReal_one]
    have he : ENNReal.ofReal (f x) ^ q * ENNReal.ofReal (f x) ^ (p - q) =
        ENNReal.ofReal (f x) ^ p := by
      rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_ne_zero_iff.mpr hx) ENNReal.ofReal_ne_top]
      congr 1
      ring
    simp only [div_eq_mul_inv,one_mul]
    rw [← mul_assoc,he,mul_comm]
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, F (x,t) ∂μ := by simp_rw [hleft]
    _ = ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), F (x,t)) ∂μ :=
      (lintegral_lintegral_swap (μ := μ) (ν := volume.restrict (Ioi (0 : ℝ)))
        (f := fun x t => F (x,t)) hF.aemeasurable).symm
    _ = _ := by
      simp_rw [hright]
      exact lintegral_const_mul _ (hf.ennreal_ofReal.pow_const p)

end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
