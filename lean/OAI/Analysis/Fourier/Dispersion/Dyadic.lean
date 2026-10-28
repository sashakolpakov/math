import OAI.Analysis.Fourier.Dispersion.Frequency
import OAI.Analysis.Fourier.LocalSmoothing.DyadicReconstruction

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

theorem integrable_dispersion_cutoff_symbol {n : ℕ} {disp : Space n → ℝ}
    (hd : Continuous disp) {χ : Space n → ℂ} (hχ : Continuous χ)
    {C : ℝ} (hC : ∀ ξ, ‖χ ξ‖ ≤ C) (h t : ℝ) (f : SchwartzMap (Space n) ℂ) :
    Integrable (fun ξ ↦ Complex.exp (-Complex.I * (t * disp ξ : ℝ)) *
      χ (h • ξ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) := by
  have hF := OAI.Analysis.Fourier.Restriction.integrable_angularFourier_schwartz f
  apply (hF.norm.const_mul C).mono'
  · exact (by fun_prop : Continuous (fun ξ : Space n ↦
      Complex.exp (-Complex.I * (t * disp ξ : ℝ)) * χ (h • ξ))).aestronglyMeasurable.mul
      hF.aestronglyMeasurable
  · filter_upwards [] with ξ
    simpa only [norm_mul, Complex.norm_exp, Complex.neg_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_mul, sub_zero, neg_zero, Real.exp_zero, one_mul] using
      mul_le_mul_of_nonneg_right (hC (h • ξ)) (norm_nonneg (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ))

theorem continuous_frequencyDispersion {n : ℕ} {disp : Space n → ℝ}
    (hd : Continuous disp) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) {h : ℝ} (hh : 0<h) (f : SchwartzMap (Space n) ℂ) :
    Continuous (fun z : Space n × ℝ ↦ frequencyDispersion disp χ h z.2 f z.1) := by
  simpa only [frequencyDispersion_eq_project disp hχ hc hh] using
    continuous_dispersionIntegral hd (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ h f)

theorem dispersion_annular_eq_sub {n : ℕ} {disp : Space n → ℝ}
    (hd : Continuous disp) (j : ℕ) (t : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    frequencyDispersion disp OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale j) t f x =
      frequencyDispersion disp OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale (j+1)) t f x -
      frequencyDispersion disp OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale j) t f x := by
  have hI (h : ℝ) := integrable_dispersion_cutoff_symbol hd
    (OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingLowCutoff n).continuous OAI.Analysis.Fourier.LocalSmoothing.norm_smoothingLowCutoff_le_one h t f
  unfold frequencyDispersion
  rw [← OAI.Analysis.Fourier.LocalSmoothing.angularInverse_sub_of_integrable (hI _) (hI _) x]
  congr 1
  funext ξ
  simp only [OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff, OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_succ, smul_smul]
  ring

theorem dispersion_dyadic_partition {n : ℕ} {disp : Space n → ℝ}
    (hd : Continuous disp) (N : ℕ) (t : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    frequencyDispersion disp OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff 1 t f x +
      ∑ j ∈ Finset.range N,
        frequencyDispersion disp OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale j) t f x =
      frequencyDispersion disp OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale N) t f x := by
  induction N with
  | zero => simp [OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale]
  | succ N hN =>
    rw [Finset.sum_range_succ, ← add_assoc, hN, dispersion_annular_eq_sub hd]
    ring

theorem tendsto_dispersion_low {n : ℕ} {disp : Space n → ℝ}
    (hd : Continuous disp) (t : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Tendsto (fun N : ℕ ↦
      frequencyDispersion disp OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale N) t f x)
      atTop (𝓝 (dispersionIntegral disp t f x)) := by
  unfold frequencyDispersion dispersionIntegral OAI.Analysis.Fourier.LocalSmoothing.angularInverse
  apply Tendsto.const_smul
  apply tendsto_integral_of_dominated_convergence (fun ξ ↦ ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ‖)
  · intro N
    exact (OAI.Analysis.Fourier.LocalSmoothing.integrable_angularKernel_mul
      (integrable_dispersion_cutoff_symbol hd (OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingLowCutoff n).continuous
        OAI.Analysis.Fourier.LocalSmoothing.norm_smoothingLowCutoff_le_one _ t f) x).aestronglyMeasurable
  · exact (OAI.Analysis.Fourier.Restriction.integrable_angularFourier_schwartz f).norm
  · intro N
    filter_upwards [] with ξ
    have H := mul_le_mul_of_nonneg_right
      (OAI.Analysis.Fourier.LocalSmoothing.norm_smoothingLowCutoff_le_one (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale N • ξ))
      (norm_nonneg (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ))
    simpa [norm_mul, Complex.norm_exp] using H
  · filter_upwards [] with ξ
    apply tendsto_const_nhds.congr'
    filter_upwards [OAI.Analysis.Fourier.LocalSmoothing.eventually_smoothingLowCutoff_dyadic_eq_one ξ] with N hN
    simp only [hN, mul_one]

theorem eLpNorm_dispersion_le_dyadic {n : ℕ} {disp : Space n → ℝ}
    (hd : Continuous disp) (f : SchwartzMap (Space n) ℂ) {p : ℝ≥0∞} (hp : 1≤p) :
    eLpNorm (fun z : Space n × ℝ ↦ dispersionIntegral disp z.2 f z.1) p (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      eLpNorm (fun z : Space n × ℝ ↦ frequencyDispersion disp OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff 1 z.2 f z.1)
        p (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) + ∑' j, eLpNorm (fun z : Space n × ℝ ↦
        frequencyDispersion disp OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale j) z.2 f z.1)
        p (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) := by
  apply OAI.Analysis.Fourier.LocalSmoothing.eLpNorm_le_base_add_tsum_of_tendsto
    (continuous_frequencyDispersion hd (OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingLowCutoff n)
      (OAI.Analysis.Fourier.LocalSmoothing.hasCompactSupport_smoothingLowCutoff n) (by norm_num) f).aestronglyMeasurable
    (fun j ↦ (continuous_frequencyDispersion hd (OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingAnnularCutoff n)
      (OAI.Analysis.Fourier.LocalSmoothing.hasCompactSupport_smoothingAnnularCutoff n) (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_pos j) f).aestronglyMeasurable)
    (continuous_dispersionIntegral hd f).aestronglyMeasurable hp
  intro z
  simpa only [dispersion_dyadic_partition hd] using tendsto_dispersion_low hd z.2 f z.1

end OAI.Analysis.Fourier.Dispersion
