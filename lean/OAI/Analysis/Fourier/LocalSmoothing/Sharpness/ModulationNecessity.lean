import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.ModulationWave
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.ModulationNonzero

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Filter
open scoped Topology ENNReal
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

/-- The modulation obstruction in Proposition `prop:sharpness`: any
uniform Sobolev local-smoothing estimate must have nonnegative order.
The proof uses actual Schwartz data and the actual half-wave integral. -/
theorem sobolev_estimate_order_nonneg {n : ℕ} (hn : 0 < n)
    {p s : ℝ} (hp : 1 ≤ p)
    (hbound : ∃ C : ℝ, ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
        ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential s f) (ENNReal.ofReal p) volume) :
    0 ≤ s := by
  by_contra hs
  have hs : s < 0 := lt_of_not_ge hs
  obtain ⟨K,hK⟩ := hbound
  obtain ⟨ω,hω,f,hf,hfs⟩ := exists_nonzero_bandlimited_bump hn
  obtain ⟨C,hC,hCb⟩ := schwartzModulation_bessel_bound n s
  let F : ℝ → Space n × ℝ → ℂ := fun N z => modulationRemainder (3*N/2) ω z.2 f z.1
  let D : ℝ≥0∞ := ENNReal.ofReal K * ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume
  have hD : D ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (f.memLp _ volume).ne
  have hFm (N : ℝ) : AEStronglyMeasurable (F N) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) :=
    (continuous_modulationRemainder (3*N/2) ω f).aestronglyMeasurable
  have hnorm (N : ℝ) : eLpNorm (F N) (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) =
      eLpNorm (fun z : Space n × ℝ =>
        OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 (schwartzModulation ((3*N/2)•ω) f) z.1)
          (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) := by
    apply eLpNorm_congr_norm_ae (hFm N)
      (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral _).aestronglyMeasurable
    exact Eventually.of_forall fun z => norm_modulationRemainder (3*N/2) ω z.2 f z.1
  have hb : ∀ᶠ N : ℝ in atTop,
      eLpNorm (F N) (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ ENNReal.ofReal (N^s) * D := by
    filter_upwards [eventually_ge_atTop (4:ℝ)] with N hN
    rw [hnorm]
    calc
      _ ≤ ENNReal.ofReal K * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential s
          (schwartzModulation ((3*N/2)•ω) f)) (ENNReal.ofReal p) volume := hK _
      _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (C*N^s) * eLpNorm f (ENNReal.ofReal p) volume) := by
        exact mul_le_mul' le_rfl (hCb N hN ω hω f hfs (ENNReal.ofReal p)
          (by simpa using ENNReal.ofReal_le_ofReal hp) ENNReal.ofReal_ne_top)
      _ = ENNReal.ofReal (N^s) * D := by
        rw [ENNReal.ofReal_mul hC]
        dsimp only [D]
        ring
  have hr : Tendsto (fun N : ℝ => N^s) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hs)
  have hright : Tendsto (fun N : ℝ => ENNReal.ofReal (N^s)*D) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr) (Or.inr hD)
    simpa only [Function.comp_def,ENNReal.ofReal_zero,mul_zero,zero_mul,mul_comm] using h
  have hzero : Tendsto (fun N : ℝ => eLpNorm (F N) (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hright
      (Eventually.of_forall fun _ => bot_le) hb
  have hscale : Tendsto (fun N : ℝ => 3*N/2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (max 0 b)] with N hN
    have hNb := (le_max_right 0 b).trans hN
    have hN0 := (le_max_left 0 b).trans hN
    linarith
  have hpoint (z : Space n × ℝ) : Tendsto (fun N => F N z) atTop (𝓝 (f (z.1-z.2•ω))) :=
    (tendsto_modulationRemainder hω f z.2 z.1).comp hscale
  have hz := eLpNorm_eq_zero_of_norm_tendsto hFm
    (by fun_prop : Continuous (fun z : Space n × ℝ => f (z.1-z.2•ω))).aestronglyMeasurable
    hpoint hzero
  exact traveling_bump_eLpNorm_ne_zero ω f hf
    (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one hp)).ne' hz

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
