import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.InputLp
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.FocalNorm
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.ModulationNecessity

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Filter
open scoped Topology ENNReal
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

theorem exponent_le_of_eventual_power_bound {a b c C : ℝ} (hc : 0 < c)
    (hb : ∀ᶠ N : ℝ in atTop, c*N^a ≤ C*N^b) : a ≤ b := by
  by_contra hn
  have hneg : b-a < 0 := by linarith
  have hnorm : ∀ᶠ N : ℝ in atTop, c ≤ C*N^(b-a) := by
    filter_upwards [hb,eventually_gt_atTop (0:ℝ)] with N hN hNp
    have hpow : 0 < N^a := Real.rpow_pos_of_pos hNp a
    calc
      c = (c*N^a)*(N^a)⁻¹ := by field_simp
      _ ≤ (C*N^b)*(N^a)⁻¹ := mul_le_mul_of_nonneg_right hN (inv_nonneg.mpr hpow.le)
      _ = C*N^(b-a) := by rw [Real.rpow_sub hNp,div_eq_mul_inv]; ring
  have hr : Tendsto (fun N : ℝ => N^(b-a)) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hneg)
  have hlim : Tendsto (fun N : ℝ => C*N^(b-a)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hr.const_mul C
  have hz : c ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hnorm
  exact (not_le_of_gt hc) hz

theorem sobolev_estimate_order_ge_focal {n : ℕ} (hn : 1 ≤ n)
    {p s : ℝ} (hp : 1 ≤ p)
    (hbound : ∃ C : ℝ, ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
        ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential s f) (ENNReal.ofReal p) volume) :
    OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n-n/p ≤ s := by
  obtain ⟨K,hK⟩ := hbound
  have hKp : 0 < |K|+1 := by positivity
  have hpp : 0 < p := lt_of_lt_of_le zero_lt_one hp
  obtain ⟨c,A,hc,hA,hlow⟩ := OAI.Analysis.Fourier.LocalSmoothing.Sharpness.focusing_packet_focal_norm_lower hn hpp
  obtain ⟨D,hD,hinput⟩ := OAI.Analysis.Fourier.LocalSmoothing.Sharpness.focusing_packet_initial_Lp hn
  obtain ⟨B,hB,hweight⟩ := sharpness_annular_bessel_bound n s
  let M := (|K|+1)*B*D
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpower : ∀ᶠ N : ℝ in atTop,
      c*N^((n:ℝ)-(n+1)/p) ≤ M*N^(s+((n:ℝ)-OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n-1/p)) := by
    filter_upwards [eventually_ge_atTop (max (8*A) 4)] with N hN
    have hNA : 8*A ≤ N := (le_max_left _ _).trans hN
    have hN4 : 4 ≤ N := (le_max_right _ _).trans hN
    have hNp : 0 < N := by linarith
    obtain ⟨f,hf,hF⟩ := OAI.Analysis.Fourier.LocalSmoothing.Sharpness.exists_focusing_packet n hNp.ne' (3/2)
    have hin := hinput p hp N (by linarith) f hf
    have hw := hweight N hN4 f (OAI.Analysis.Fourier.LocalSmoothing.Sharpness.focusing_packet_annular hNp hF)
      (ENNReal.ofReal p) (by simpa using ENNReal.ofReal_le_ofReal hp) ENNReal.ofReal_ne_top
    have hK' : ENNReal.ofReal K ≤ ENNReal.ofReal (|K|+1) :=
      ENNReal.ofReal_le_ofReal (by linarith [le_abs_self K])
    have hh := (hlow N hNA f hF).trans ((hK f).trans
      (mul_le_mul' hK' (hw.trans (mul_le_mul' le_rfl hin))))
    have he : ENNReal.ofReal (|K|+1) * (ENNReal.ofReal (B*N^s) *
        ENNReal.ofReal (D*N^((n:ℝ)-OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n-1/p))) =
        ENNReal.ofReal (M*N^(s+((n:ℝ)-OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n-1/p))) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hB (Real.rpow_nonneg hNp.le _)),
        ← ENNReal.ofReal_mul hKp.le,Real.rpow_add hNp]
      congr 1
      dsimp only [M]
      ring
    rw [he] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hM (Real.rpow_nonneg hNp.le _))).mp hh
  have hexp := exponent_le_of_eventual_power_bound hc hpower
  have he : ((n:ℝ)+1)/p = n/p+1/p := add_div _ _ _
  linarith

/-- The full necessary Sobolev power in Proposition `prop:sharpness`. -/
theorem sobolev_estimate_sharp_order {n : ℕ} (hn : 2 ≤ n)
    {p s : ℝ} (hp : 2 ≤ p)
    (hbound : ∃ C : ℝ, ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
        ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential s f) (ENNReal.ofReal p) volume) :
    OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p ≤ s := by
  apply max_le
  · exact sobolev_estimate_order_nonneg (by omega) (by linarith) hbound
  · exact sobolev_estimate_order_ge_focal (by omega) (by linarith) hbound

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
