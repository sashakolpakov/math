import OAI.Analysis.Fourier.BochnerRiesz.AllTime
import OAI.Analysis.Fourier.SquareFunction.Shell

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem continuous_radiusSuperposition {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (φ : SchwartzMap ℝ ℂ) (δ : ℝ) {R : X → ℝ}
    (hR : Measurable R) {a : X → ℂ} (ha : Integrable a μ) :
    Continuous (OAI.Analysis.Fourier.SquareFunction.radiusSuperposition μ φ δ R a) := by
  let B := SchwartzMap.seminorm ℝ 0 0 φ
  have hm (s : ℝ) : AEStronglyMeasurable (fun ξ ↦ φ ((s - R ξ) / δ) * a ξ) μ :=
    (φ.continuous.measurable.comp ((measurable_const.sub hR).div_const δ)).aestronglyMeasurable.mul
      ha.aestronglyMeasurable
  have hb (s : ℝ) (ξ : X) : ‖φ ((s - R ξ) / δ) * a ξ‖ ≤ B * ‖a ξ‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ φ _) (norm_nonneg _)
  apply continuous_iff_continuousAt.mpr
  intro s
  apply tendsto_integral_filter_of_dominated_convergence (fun ξ ↦ B * ‖a ξ‖)
  · exact Filter.Eventually.of_forall hm
  · exact Filter.Eventually.of_forall fun t ↦ Filter.Eventually.of_forall (hb t)
  · exact ha.norm.const_mul B
  · exact Filter.Eventually.of_forall fun ξ ↦
      ((φ.continuous.comp ((continuous_id.sub continuous_const).div_const δ)).mul
        continuous_const).tendsto s

theorem norm_halfWaveIntegral_le_fourierL1 {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    (t : ℝ) (x : Space n) :
    ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ ≤ ∫ ξ : Space n, ‖(𝓕 f) ξ‖ := by
  rw [OAI.Analysis.Fourier.SquareFunction.halfWaveIntegral_eq_spatialPhase]
  apply norm_integral_le_of_norm_le (𝓕 f).integrable.norm
  exact Filter.Eventually.of_forall fun ξ ↦ by
    simp [OAI.Analysis.Fourier.SquareFunction.radiusPhase, OAI.Analysis.Fourier.SquareFunction.spatialPhase, Complex.norm_exp]

theorem integrable_fourierCutoff_dilate (φ : SchwartzMap ℝ ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : ℝ ↦ (𝓕 φ : SchwartzMap ℝ ℂ) (δ * t)) := by
  simpa only [sub_zero, div_inv_eq_mul, mul_comm] using
    OAI.Analysis.Fourier.SquareFunction.integrable_radius_shift_dilate (𝓕 φ : SchwartzMap ℝ ℂ).integrable 0 (inv_ne_zero hδ.ne')

theorem continuous_time_halfWave {n : ℕ} (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Continuous (fun t : ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x) := by
  have hc : Continuous (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1) :=
    OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral (n := n) f
  have hg : Continuous (fun t : ℝ ↦ (x, t)) := continuous_const.prodMk continuous_id
  have H := hc.comp hg
  simpa only [Function.comp_def] using H

theorem integrable_time_weight_mul_halfWave {n : ℕ} {a : ℝ → ℂ} (ha : Integrable a)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Integrable (fun t : ℝ ↦ a t * OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x) := by
  have hm : AEStronglyMeasurable (fun t : ℝ ↦ a t * OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x) volume :=
    ha.aestronglyMeasurable.mul (continuous_time_halfWave f x).aestronglyMeasurable
  apply (ha.norm.mul_const (∫ ξ : Space n, ‖(𝓕 f : SchwartzMap (Space n) ℂ) ξ‖)).mono' hm
  exact Filter.Eventually.of_forall fun t ↦ by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_halfWaveIntegral_le_fourierL1 (n := n) f t x) (norm_nonneg _)

theorem integrable_fourierCutoff_mul_halfWave {n : ℕ} (φ : SchwartzMap ℝ ℂ)
    {δ : ℝ} (hδ : 0 < δ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Integrable (fun t : ℝ ↦ (𝓕 φ : SchwartzMap ℝ ℂ) (δ * t) * OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x) :=
  integrable_time_weight_mul_halfWave (integrable_fourierCutoff_dilate φ hδ) f x

theorem continuous_fourierInv_of_integrable {n : ℕ} {g : Space n → ℂ} (hg : Integrable g) :
    Continuous (𝓕⁻ g) := by
  have hc : Continuous (𝓕 g) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hg
  have he : 𝓕⁻ g = (fun x : Space n ↦ 𝓕 g (-x)) :=
    funext (Real.fourierInv_eq_fourier_neg g)
  rw [he]
  have H := hc.comp (continuous_neg : Continuous (fun x : Space n ↦ -x))
  simpa only [Function.comp_def] using H

theorem integrable_thinShellCycles_symbol {n : ℕ} (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (s : ℝ) :
    Integrable (fun ξ : Space n ↦ φ ((s - ‖ξ‖) / δ) * (𝓕 f : SchwartzMap (Space n) ℂ) ξ) := by
  have hc : Continuous (fun ξ : Space n ↦ φ ((s - ‖ξ‖) / δ) * (𝓕 f : SchwartzMap (Space n) ℂ) ξ) := by
    fun_prop
  apply ((𝓕 f : SchwartzMap (Space n) ℂ).integrable.norm.const_mul
    (SchwartzMap.seminorm ℝ 0 0 φ)).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ ↦ by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ φ _) (norm_nonneg _)

theorem continuous_thinShellCycles_space {n : ℕ} (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (s : ℝ) :
    Continuous (fun x : Space n ↦ OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ δ f x s) :=
  continuous_fourierInv_of_integrable (integrable_thinShellCycles_symbol φ δ f s)

/-- An exact wave-superposition formula for a thin radial multiplier.
The radius and the temporal variable use the cycles Fourier convention. -/
theorem thinShellCycles_eq_wave_integral {n : ℕ} (φ : SchwartzMap ℝ ℂ)
    {δ : ℝ} (hδ : 0 < δ) (f : SchwartzMap (Space n) ℂ) (x : Space n) (s : ℝ) :
    OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ δ f x s =
      ∫ t : ℝ, Complex.exp ((2 * Real.pi * t * s : ℝ) * Complex.I) *
        ((δ : ℂ) * (𝓕 φ) (δ * t) * OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x) := by
  have hc : Continuous (OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ δ f x) := by
    rw [OAI.Analysis.Fourier.SquareFunction.thinShellCycles_eq_radiusSuperposition]
    exact continuous_radiusSuperposition volume φ δ continuous_norm.measurable
      (OAI.Analysis.Fourier.SquareFunction.integrable_spatialPhase_mul x (𝓕 f).integrable)
  have hfour : 𝓕 (OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ δ f x) =
      fun t : ℝ ↦ (δ : ℂ) * (𝓕 φ) (δ * t) * OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x :=
    funext (OAI.Analysis.Fourier.SquareFunction.fourier_thinShellCycles φ hδ f x)
  have hi : Integrable (𝓕 (OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ δ f x)) := by
    rw [hfour]
    simpa only [mul_assoc] using
      (integrable_fourierCutoff_mul_halfWave φ hδ f x).const_mul (δ : ℂ)
  rw [← (OAI.Analysis.Fourier.SquareFunction.integrable_thinShellCycles φ hδ f x).fourierInv_fourier_eq hi hc.continuousAt,
    hfour, Real.fourierInv_eq']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t ↦ by
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring_nf

end OAI.Analysis.Fourier.BochnerRiesz
