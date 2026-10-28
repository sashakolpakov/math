import OAI.Analysis.Fourier.WavePackets.PeriodicKernel
import OAI.Analysis.Fourier.WavePackets.KernelIdentity

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal FourierTransform ContDiff

noncomputable local instance sectorCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance sectorCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance sectorCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance sectorTorusNegInvariant (n : ℕ) : (volume : Measure (UnitAddTorus (Fin n))).IsNegInvariant := by
  constructor
  exact (measurePreserving_pi (fun _ : Fin n => (volume : Measure UnitAddCircle))
    (fun _ : Fin n => (volume : Measure UnitAddCircle)) (fun _ => Measure.measurePreserving_neg volume)).map_eq

noncomputable def periodicSchwartzKernel {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hz : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ :=
  𝓕⁻ (periodicSchwartzSymbol hs hφ hz hh T)

/-- The actual Fourier-series operator is convolution by the periodized
inverse symbol. Physical side-length factors cancel exactly. -/
theorem periodicHalfWave_eq_periodized_convolution {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hz : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) {f : UnitAddTorus (Fin n) → ℂ}
    (hf : Integrable f) :
    periodicHalfWave φ h T f = complexConvolution
      (latticePeriodization (periodicSchwartzKernel hs hφ hz hh T)) f volume := by
  let K : EuclideanSpace ℝ (Fin n) → ℂ := periodicSchwartzKernel hs hφ hz hh T
  have hk (z : UnitAddTorus (Fin n)) : periodicKernel φ h T z =
      ((100 : ℂ) ^ n)⁻¹ * latticePeriodization K z := by
    obtain ⟨y, rfl⟩ := torusProjection_surjective z
    rw [periodicKernel_eq_inverseSymbol_sum hs hφ hz hh, latticePeriodization_projection,
      tsum_mul_left]
    rfl
  funext x
  rw [periodicHalfWave_eq_kernel_integral hs hh T hf]
  simp_rw [hk, mul_assoc]
  rw [integral_const_mul, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero n (by norm_num)), one_mul]
  change (∫ y, latticePeriodization K (x - y) * f y) =
    ∫ y, latticePeriodization K y * f (x - y)
  simpa only [sub_sub_cancel] using integral_sub_left_eq_self
    (fun y => latticePeriodization K y * f (x - y)) volume x

/-- The unit-torus symbol at zero time is just a positive scalar frequency
rescaling; its inverse Fourier kernel has the original L1 norm. -/
theorem periodicSchwartzSymbol_zero_kernel_norm {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hz : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    {h : ℝ} (hh : 0 < h) :
    eLpNorm (periodicSchwartzKernel hs hφ hz hh 0) 1 volume =
      eLpNorm (𝓕⁻ φ) 1 volume := by
  let a := h * (2 * Real.pi / 100)
  have ha : a ≠ 0 := by dsimp [a]; positivity
  let A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := EuclideanSpace ℝ (Fin n)) (Units.mk0 a ha)
  have he : (periodicSchwartzSymbol hs hφ hz hh 0 : EuclideanSpace ℝ (Fin n) → ℂ) = φ ∘ A := by
    funext ξ
    change waveAmplitude φ h 0 (a • ξ) = φ (a • ξ)
    simp [waveAmplitude]
  have hi : Measurable (𝓕⁻ φ) := by
    have heq : ((𝓕⁻ (hs.toSchwartzMap hφ) : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
        EuclideanSpace ℝ (Fin n) → ℂ) = 𝓕⁻ φ := by
      rw [SchwartzMap.fourierInv_coe]
      rfl
    rw [← heq]
    exact (𝓕⁻ (hs.toSchwartzMap hφ)).continuous.measurable
  unfold periodicSchwartzKernel
  rw [SchwartzMap.fourierInv_coe, he]
  exact eLpNorm_fourierInv_comp_linearEquiv A φ hi

/-- Uniform in the semiclassical scale, the actual periodic cutoff has
operator norm at most the L1 norm of the unscaled inverse symbol. -/
theorem periodic_cutoff_norm_bound {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hz : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    {h : ℝ} (hh : 0 < h) {f : UnitAddTorus (Fin n) → ℂ}
    (hf : Measurable f) (hfi : Integrable f) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤) :
    eLpNorm (periodicHalfWave φ h 0 f) p volume ≤
      eLpNorm (𝓕⁻ φ) 1 volume * eLpNorm f p volume := by
  rw [periodicHalfWave_eq_periodized_convolution hs hφ hz hh 0 hfi]
  have hb := eLpNorm_periodized_convolution_le
    (periodicSchwartzKernel hs hφ hz hh 0).continuous.measurable hf hp hp_top
  rwa [periodicSchwartzSymbol_zero_kernel_norm hs hφ hz hh] at hb

/-- The endpoint bound required after applying a sector projection to an
amplitude shell. The input bound is pointwise and the output is the genuine
Fourier multiplier, not a separately postulated operator. -/
theorem periodic_cutoff_top_norm_bound {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hz : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    {h : ℝ} (hh : 0 < h) {f : UnitAddTorus (Fin n) → ℂ}
    (hf : Measurable f) (hfi : Integrable f) {B : ℝ≥0∞}
    (hb : ∀ x, ‖f x‖ₑ ≤ B) :
    eLpNorm (periodicHalfWave φ h 0 f) ⊤ volume ≤ eLpNorm (𝓕⁻ φ) 1 volume * B := by
  rw [periodicHalfWave_eq_periodized_convolution hs hφ hz hh 0 hfi]
  have he := eLpNorm_periodized_convolution_top_le
    (periodicSchwartzKernel hs hφ hz hh 0).continuous.measurable hf hb
  rwa [periodicSchwartzSymbol_zero_kernel_norm hs hφ hz hh] at he

end OAI.Analysis.Fourier.WavePackets
