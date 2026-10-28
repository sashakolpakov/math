import OAI.Analysis.Fourier.SquareFunction.Shell.L2

/-! Lebesgue-measure bookkeeping for the passage from radius blocks `[1,2]`
to the full Stein square function with measure `dr/r`. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal

theorem setLIntegral_radius_dilate {a : ℝ} (ha : 0 < a)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ r in Icc a (2 * a), F r) =
      ENNReal.ofReal a * ∫⁻ s in Icc (1 : ℝ) 2, F (a * s) := by
  have hm (s : ℝ) : a * s ∈ Icc a (2 * a) ↔ s ∈ Icc (1 : ℝ) 2 := by
    change (a ≤ a * s ∧ a * s ≤ 2 * a) ↔ (1 ≤ s ∧ s ≤ 2)
    rw [mul_comm 2 a]
    constructor
    · intro h
      exact ⟨(mul_le_mul_iff_right₀ ha).mp (by simpa using h.1), (mul_le_mul_iff_right₀ ha).mp h.2⟩
    · intro h
      exact ⟨by simpa using mul_le_mul_of_nonneg_left h.1 ha.le,
        mul_le_mul_of_nonneg_left h.2 ha.le⟩
  have he : (fun s => (Icc a (2 * a)).indicator F (a * s)) =
      (Icc (1 : ℝ) 2).indicator (fun s => F (a * s)) := by
    funext s
    by_cases hs : s ∈ Icc (1 : ℝ) 2 <;> simp [indicator, hm, hs]
  have hd := lintegral_dilate_real ((Icc a (2 * a)).indicator F)
    (hF.indicator measurableSet_Icc) ha
  rw [he, lintegral_indicator measurableSet_Icc, lintegral_indicator measurableSet_Icc] at hd
  have hc : ENNReal.ofReal a * ENNReal.ofReal a⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul ha.le, mul_inv_cancel₀ ha.ne', ENNReal.ofReal_one]
  calc
    _ = ENNReal.ofReal a * (ENNReal.ofReal a⁻¹ * ∫⁻ r in Icc a (2 * a), F r) := by
      rw [← mul_assoc, hc, one_mul]
    _ = _ := congrArg (fun z => ENNReal.ofReal a * z) hd.symm

theorem setLIntegral_radius_ratio_dilate {a : ℝ} (ha : 0 < a)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ r in Icc a (2 * a), F r / ENNReal.ofReal r) =
      ∫⁻ s in Icc (1 : ℝ) 2, F (a * s) / ENNReal.ofReal s := by
  have hm : Measurable (fun r => F r / ENNReal.ofReal r) :=
    hF.div ENNReal.continuous_ofReal.measurable
  rw [setLIntegral_radius_dilate ha (fun r => F r / ENNReal.ofReal r) hm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro s
  rw [ENNReal.ofReal_mul ha.le, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv]
  calc
    _ = (ENNReal.ofReal a * (ENNReal.ofReal a)⁻¹) *
        (F (a * s) * (ENNReal.ofReal s)⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top, one_mul]
  all_goals simp

theorem radius_ratio_dyadic_bound (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ r in Ioi (0 : ℝ), F r / ENNReal.ofReal r) ≤
      ∑' k : ℤ, ∫⁻ s in Icc (1 : ℝ) 2, F ((2 : ℝ) ^ k * s) := by
  have hcover : Ioi (0 : ℝ) ⊆ ⋃ k : ℤ, Icc ((2 : ℝ) ^ k) (2 * (2 : ℝ) ^ k) := by
    intro r hr
    obtain ⟨k, hlo, hhi⟩ := exists_mem_Ico_zpow hr (by norm_num : (1 : ℝ) < 2)
    apply mem_iUnion.mpr
    refine ⟨k, hlo, ?_⟩
    simpa only [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, mul_comm] using hhi.le
  calc
    _ ≤ ∫⁻ r in ⋃ k : ℤ, Icc ((2 : ℝ) ^ k) (2 * (2 : ℝ) ^ k),
        F r / ENNReal.ofReal r := lintegral_mono_set hcover
    _ ≤ ∑' k : ℤ, ∫⁻ r in Icc ((2 : ℝ) ^ k) (2 * (2 : ℝ) ^ k),
        F r / ENNReal.ofReal r := lintegral_iUnion_le _ _
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro k
      rw [setLIntegral_radius_ratio_dilate (by positivity) F hF]
      apply setLIntegral_mono' measurableSet_Icc
      intro s hs
      have hden : 1 ≤ ENNReal.ofReal s := by simpa using ENNReal.ofReal_le_ofReal hs.1
      calc
        _ ≤ F ((2 : ℝ) ^ k * s) / 1 := ENNReal.div_le_div_left hden _
        _ = _ := div_one _

theorem measurable_first_section {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {F : X × Y → Z} (hF : Measurable F) (y : Y) :
    Measurable (fun x => F (x, y)) :=
  hF.comp (measurable_id.prodMk measurable_const)

theorem radius_square_dyadic_bound (F : ℝ → ℂ) (hF : Measurable F) :
    (∫⁻ r in Ioi (0 : ℝ), ‖F r‖ₑ ^ (2 : ℝ) / ENNReal.ofReal r) ^ (1 / 2 : ℝ) ≤
      (∑' k : ℤ, eLpNorm (fun s => F ((2 : ℝ) ^ k * s))
        2 (volume.restrict (Icc (1 : ℝ) 2)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hb := radius_ratio_dyadic_bound (fun r => ‖F r‖ₑ ^ (2 : ℝ))
    (hF.enorm.pow_const (2 : ℝ))
  have he (k : ℤ) :
      eLpNorm (fun s => F ((2 : ℝ) ^ k * s))
          2 (volume.restrict (Icc (1 : ℝ) 2)) ^ (2 : ℝ) =
        ∫⁻ s in Icc (1 : ℝ) 2, ‖F ((2 : ℝ) ^ k * s)‖ₑ ^ (2 : ℝ) :=
    eLpNorm_two_rpow_general _ (hF.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
  simp_rw [he]
  exact ENNReal.rpow_le_rpow hb (by norm_num)

end OAI.Analysis.Fourier.SquareFunction
