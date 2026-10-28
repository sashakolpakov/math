import OAI.Analysis.Fourier.BochnerRiesz.DyadicTime

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

def positiveTimeMeasure (n : ℕ) : Measure (Space n × ℝ) :=
  volume.prod (volume.restrict (Set.Ioi 0))

theorem positive_weighted_bound_from_slabs {p σ M : ℝ}
    (hp : 0 < p) (hσ : 0 ≤ σ) (hM : 1 / p + σ < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ F : Space n × ℝ → ℂ, Continuous F → ∀ B : ℝ≥0∞,
      (∀ r : ℝ, 0 < r → eLpNorm F (ENNReal.ofReal p) (timeSlabMeasure n r) ≤
        ENNReal.ofReal (r ^ (1 / p) * (max 1 r) ^ σ) * B) →
      eLpNorm (weightedTimeFunction M F) (ENNReal.ofReal p) (positiveTimeMeasure n) ≤
        ENNReal.ofReal C * B := by
  let e : ℝ := 1 / p + σ - M
  have he : e < 0 := sub_neg.mpr hM
  have hM0 : 0 ≤ M := by have := one_div_pos.mpr hp; linarith
  let a : ℝ≥0∞ := ENNReal.ofReal (2 ^ (e * p))
  have ha : a < 1 := by
    apply ENNReal.ofReal_lt_one.mpr
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (mul_neg_of_neg_of_pos he hp)
  let D : ℝ≥0∞ := (∑' k : ℕ, (1 / 2 : ℝ≥0∞) ^ (k + 1)) + (∑' k : ℕ, a ^ k)
  have hsmall : (∑' k : ℕ, (1 / 2 : ℝ≥0∞) ^ (k + 1)) < ⊤ := by
    simp only [pow_succ, ENNReal.tsum_mul_right]
    exact ENNReal.mul_lt_top (tsum_geometric_lt_top.mpr (by norm_num)) (by norm_num)
  have hD : D < ⊤ := ENNReal.add_lt_top.mpr ⟨hsmall, tsum_geometric_lt_top.mpr ha⟩
  let S : ℝ≥0∞ := D ^ (1 / p)
  have hS : S ≠ ⊤ := (ENNReal.rpow_lt_top_of_nonneg (by positivity) hD.ne).ne
  have hSb : S ≤ ENNReal.ofReal (S.toReal + 1) := by
    rw [← ENNReal.ofReal_toReal hS]
    exact ENNReal.ofReal_le_ofReal (by simp)
  refine ⟨S.toReal + 1, by positivity, ?_⟩
  intro n F hF B hb
  have hWF := continuous_weightedTimeFunction M hF
  have H := dyadic_norm_bounds_imply_positive_moment hWF hp e B
    (fun k ↦ weighted_small_slab_bound hF hM0
      (by unfold smallTimeRadius; positivity)
      (by unfold smallTimeRadius; exact pow_le_one₀ (by norm_num) (by norm_num))
      (hb _ (by unfold smallTimeRadius; positivity)))
    (fun k ↦ weighted_large_slab_bound hF hM0
      (by unfold largeTimeRadius; exact one_le_pow₀ (by norm_num))
      (hb _ (by unfold largeTimeRadius; positivity)))
  rw [time_section_moment_eq hWF hp] at H
  have Hn := ENNReal.rpow_le_rpow H (show 0 ≤ 1 / p by positivity)
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (show 0 ≤ 1 / p by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one] at Hn
  change eLpNorm (weightedTimeFunction M F) (ENNReal.ofReal p) (positiveTimeMeasure n) ≤ B * S at Hn
  exact Hn.trans ((mul_le_mul' (le_refl B) hSb).trans_eq (mul_comm B _))

theorem localSmoothing_positive_weighted (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    {p ε M : ℝ} (hp : 2 ≤ p) (hε : 0 < ε)
    (hM : 1 / p + (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε) < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) →
      eLpNorm (weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1))
        (ENNReal.ofReal p) (positiveTimeMeasure n) ≤
      ENNReal.ofReal (C * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨A, hA, ha⟩ := localSmoothing_all_positive_slabs hls hn hχ hc hzero hp hε
  have hp0 : 0 < p := by linarith
  have hσ : 0 ≤ OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε := add_nonneg (le_max_left _ _) hε.le
  obtain ⟨D, hD, hd⟩ := positive_weighted_bound_from_slabs hp0 hσ hM
  refine ⟨D * A, mul_pos hD hA, ?_⟩
  intro h hh hone f hcut
  have hf := OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f
  have HB := hd n _ hf
    (ENNReal.ofReal (A * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) * eLpNorm f (ENNReal.ofReal p) volume)
  have HS : ∀ r : ℝ, 0 < r →
      eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (timeSlabMeasure n r) ≤
      ENNReal.ofReal (r ^ (1 / p) * (max 1 r) ^ (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)) *
        (ENNReal.ofReal (A * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) * eLpNorm f (ENNReal.ofReal p) volume) := by
    intro r hr
    convert ha h r hh hone hr f hcut using 1
    simp only [ENNReal.ofReal_mul hA.le,
      ENNReal.ofReal_mul (mul_nonneg hA.le (Real.rpow_nonneg hr.le _)),
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hA.le (Real.rpow_nonneg hr.le _))
        (Real.rpow_nonneg hh.le _)), ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
    ac_rfl
  have H := HB HS
  convert H using 1
  rw [ENNReal.ofReal_mul (mul_nonneg hD.le hA.le), ENNReal.ofReal_mul hD.le,
    ENNReal.ofReal_mul hA.le]
  ac_rfl

end OAI.Analysis.Fourier.BochnerRiesz
