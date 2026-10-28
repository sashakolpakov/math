import OAI.Analysis.Fourier.LocalSmoothing.DyadicCutoff
import OAI.Analysis.Fourier.LocalSmoothing.L2
import OAI.Analysis.Fourier.Restriction.FourierProduct
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing

theorem integrable_angularKernel_mul {n : ℕ} {g : Space n → ℂ}
    (hg : Integrable g) (x : Space n) :
    Integrable (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * g ξ) := by
  apply hg.norm.mono'
  · exact (by fun_prop : Continuous (fun ξ : Space n ↦
      Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)))).aestronglyMeasurable.mul
      hg.aestronglyMeasurable
  · filter_upwards [] with ξ
    simp [Complex.norm_exp]

theorem angularInverse_sub_of_integrable {n : ℕ} {g k : Space n → ℂ}
    (hg : Integrable g) (hk : Integrable k) (x : Space n) :
    angularInverse (fun ξ ↦ g ξ - k ξ) x = angularInverse g x - angularInverse k x := by
  simp only [angularInverse, mul_sub,
    integral_sub (integrable_angularKernel_mul hg x) (integrable_angularKernel_mul hk x), smul_sub]

theorem integrable_wave_cutoff_symbol {n : ℕ} {χ : Space n → ℂ}
    (hχ : Continuous χ) {C : ℝ} (hC : ∀ ξ, ‖χ ξ‖ ≤ C)
    (h t : ℝ) (f : SchwartzMap (Space n) ℂ) :
    Integrable (fun ξ ↦ Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) *
      χ (h • ξ) * angularFourier f ξ) := by
  have hF := OAI.Analysis.Fourier.Restriction.integrable_angularFourier_schwartz f
  apply (hF.norm.const_mul C).mono'
  · exact (by fun_prop : Continuous (fun ξ : Space n ↦
      Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) * χ (h • ξ))).aestronglyMeasurable.mul
      hF.aestronglyMeasurable
  · filter_upwards [] with ξ
    simpa only [norm_mul, Complex.norm_exp, Complex.neg_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_mul, sub_zero, neg_zero, Real.exp_zero, one_mul] using
      mul_le_mul_of_nonneg_right (hC (h • ξ)) (norm_nonneg (angularFourier f ξ))

theorem halfWaveIntegral_projected {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h : ℝ} (hh : 0 < h)
    (f : SchwartzMap (Space n) ℂ) (t : ℝ) (x : Space n) :
    halfWaveIntegral t (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ h f) x =
      frequencyHalfWave χ h t f x := by
  simp only [halfWaveIntegral, frequencyHalfWave,
    OAI.Analysis.Fourier.BochnerRiesz.angularFourier_annularProject hχ hc hh f, mul_assoc]

theorem continuous_frequencyHalfWave_schwartz {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h : ℝ} (hh : 0 < h)
    (f : SchwartzMap (Space n) ℂ) :
    Continuous (fun z : Space n × ℝ ↦ frequencyHalfWave χ h z.2 f z.1) := by
  simpa only [halfWaveIntegral_projected hχ hc hh f] using
    continuous_halfWaveIntegral (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ h f)

theorem smoothing_annular_wave_eq_sub {n : ℕ} (j : ℕ) (t : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    frequencyHalfWave smoothingAnnularCutoff (smoothingDyadicScale j) t f x =
      frequencyHalfWave smoothingLowCutoff (smoothingDyadicScale (j + 1)) t f x -
      frequencyHalfWave smoothingLowCutoff (smoothingDyadicScale j) t f x := by
  have hI (h : ℝ) := integrable_wave_cutoff_symbol (contDiff_smoothingLowCutoff n).continuous
    norm_smoothingLowCutoff_le_one h t f
  unfold frequencyHalfWave
  rw [← angularInverse_sub_of_integrable (hI _) (hI _) x]
  congr 1
  funext ξ
  simp only [smoothingAnnularCutoff, smoothingDyadicScale_succ, smul_smul]
  ring

/-- The actual half-wave integrals obey the finite telescoping decomposition. -/
theorem smoothing_wave_dyadic_partition {n : ℕ} (N : ℕ) (t : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    frequencyHalfWave smoothingLowCutoff 1 t f x +
      ∑ j ∈ Finset.range N,
        frequencyHalfWave smoothingAnnularCutoff (smoothingDyadicScale j) t f x =
      frequencyHalfWave smoothingLowCutoff (smoothingDyadicScale N) t f x := by
  induction N with
  | zero => simp [smoothingDyadicScale]
  | succ N hN =>
    rw [Finset.sum_range_succ, ← add_assoc, hN, smoothing_annular_wave_eq_sub]
    ring

/-- Dominated convergence removes the low-pass truncation for the literal
Fourier-integral propagator, pointwise in both space and time. -/
theorem tendsto_smoothing_low_wave {n : ℕ} (t : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Tendsto (fun N : ℕ ↦
      frequencyHalfWave smoothingLowCutoff (smoothingDyadicScale N) t f x)
      atTop (𝓝 (halfWaveIntegral t f x)) := by
  unfold frequencyHalfWave halfWaveIntegral angularInverse
  apply Tendsto.const_smul
  apply tendsto_integral_of_dominated_convergence (fun ξ ↦ ‖angularFourier f ξ‖)
  · intro N
    exact (integrable_angularKernel_mul
      (integrable_wave_cutoff_symbol (contDiff_smoothingLowCutoff n).continuous
        norm_smoothingLowCutoff_le_one _ t f) x).aestronglyMeasurable
  · exact (OAI.Analysis.Fourier.Restriction.integrable_angularFourier_schwartz f).norm
  · intro N
    filter_upwards [] with ξ
    have H := mul_le_mul_of_nonneg_right
      (norm_smoothingLowCutoff_le_one (smoothingDyadicScale N • ξ))
      (norm_nonneg (angularFourier f ξ))
    simpa [norm_mul, Complex.norm_exp] using H
  · filter_upwards [] with ξ
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_smoothingLowCutoff_dyadic_eq_one ξ] with N hN
    simp only [hN, mul_one]

theorem tendsto_smoothing_wave_dyadic_partition {n : ℕ} (t : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Tendsto (fun N : ℕ ↦ frequencyHalfWave smoothingLowCutoff 1 t f x +
      ∑ j ∈ Finset.range N,
        frequencyHalfWave smoothingAnnularCutoff (smoothingDyadicScale j) t f x)
      atTop (𝓝 (halfWaveIntegral t f x)) := by
  simpa only [smoothing_wave_dyadic_partition] using tendsto_smoothing_low_wave t f x

theorem eLpNorm_le_base_add_tsum_of_tendsto {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {u₀ v : X → E} {u : ℕ → X → E}
    (h₀ : AEStronglyMeasurable u₀ μ) (hu : ∀ j, AEStronglyMeasurable (u j) μ)
    (hv : AEStronglyMeasurable v μ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hlim : ∀ x, Tendsto (fun N ↦ u₀ x + ∑ j ∈ Finset.range N, u j x)
      atTop (𝓝 (v x))) :
    eLpNorm v p μ ≤ eLpNorm u₀ p μ + ∑' j, eLpNorm (u j) p μ := by
  apply Lp.eLpNorm_le_of_ae_tendsto
    (f := fun N x ↦ u₀ x + ∑ j ∈ Finset.range N, u j x)
    (Eventually.of_forall fun N ↦ ?_)
    (fun N ↦ h₀.add (Finset.aestronglyMeasurable_fun_sum _ (fun j _ ↦ hu j))) hv
    (Eventually.of_forall hlim)
  have he : (fun x ↦ u₀ x + ∑ j ∈ Finset.range N, u j x) =
      u₀ + ∑ j ∈ Finset.range N, u j := by
    funext x
    simp only [Pi.add_apply, Finset.sum_apply]
  rw [he]
  calc
    eLpNorm (u₀ + ∑ j ∈ Finset.range N, u j) p μ ≤
        eLpNorm u₀ p μ + eLpNorm (∑ j ∈ Finset.range N, u j) p μ :=
      eLpNorm_add_le (μ := μ) (p := p) (f := u₀)
        (g := ∑ j ∈ Finset.range N, u j) hp
    _ ≤ eLpNorm u₀ p μ + ∑ j ∈ Finset.range N, eLpNorm (u j) p μ :=
      add_le_add le_rfl (eLpNorm_sum_le (μ := μ) (p := p) (f := u)
        (s := Finset.range N) hp)
    _ ≤ eLpNorm u₀ p μ + ∑' j, eLpNorm (u j) p μ :=
      add_le_add le_rfl (ENNReal.sum_le_tsum (s := Finset.range N)
        (f := fun j ↦ eLpNorm (u j) p μ))

theorem aestronglyMeasurable_smoothing_low {n : ℕ}
    (f : SchwartzMap (Space n) ℂ) {h : ℝ} (hh : 0 < h) :
    AEStronglyMeasurable (fun z : Space n × ℝ ↦
      frequencyHalfWave smoothingLowCutoff h z.2 f z.1) (observationMeasure n) :=
  (continuous_frequencyHalfWave_schwartz (n := n) (χ := @smoothingLowCutoff n)
    (h := h) (contDiff_smoothingLowCutoff n) (hasCompactSupport_smoothingLowCutoff n)
    hh f).aestronglyMeasurable

theorem aestronglyMeasurable_smoothing_annular {n : ℕ}
    (f : SchwartzMap (Space n) ℂ) (j : ℕ) :
    AEStronglyMeasurable (fun z : Space n × ℝ ↦
      frequencyHalfWave smoothingAnnularCutoff (smoothingDyadicScale j) z.2 f z.1)
      (observationMeasure n) :=
  (continuous_frequencyHalfWave_schwartz (n := n) (χ := @smoothingAnnularCutoff n)
    (h := smoothingDyadicScale j) (contDiff_smoothingAnnularCutoff n)
    (hasCompactSupport_smoothingAnnularCutoff n) (smoothingDyadicScale_pos j) f).aestronglyMeasurable

/-- The dyadic triangle inequality for the actual solution. No summability
assumption is hidden here: the right side is an extended nonnegative sum. -/
theorem eLpNorm_halfWave_le_dyadic {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) p (observationMeasure n) ≤
      eLpNorm (fun z : Space n × ℝ ↦ frequencyHalfWave smoothingLowCutoff 1 z.2 f z.1)
        p (observationMeasure n) +
      ∑' j, eLpNorm (fun z : Space n × ℝ ↦
        frequencyHalfWave smoothingAnnularCutoff (smoothingDyadicScale j) z.2 f z.1)
        p (observationMeasure n) := by
  exact eLpNorm_le_base_add_tsum_of_tendsto
    (aestronglyMeasurable_smoothing_low f (by norm_num))
    (aestronglyMeasurable_smoothing_annular f)
    (continuous_halfWaveIntegral f).aestronglyMeasurable hp
    (fun z ↦ tendsto_smoothing_wave_dyadic_partition z.2 f z.1)

end OAI.Analysis.Fourier.LocalSmoothing
