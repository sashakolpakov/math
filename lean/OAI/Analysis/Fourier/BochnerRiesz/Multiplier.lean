import OAI.Analysis.Fourier.BochnerRiesz.Dilation
import OAI.Analysis.Fourier.BochnerRiesz.Kernel
import OAI.Analysis.Fourier.WavePackets.ConvolutionIdentity

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal ContDiff

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem eLpNorm_normalized_dilate_one {n : ℕ} (K : Space n → ℂ) (hK : Measurable K)
    {h : ℝ} (hh : 0 < h) :
    eLpNorm (fun x ↦ (h ^ n)⁻¹ • K (h⁻¹ • x)) 1 volume = eLpNorm K 1 volume := by
  change eLpNorm ((h ^ n)⁻¹ • (fun x ↦ K (h⁻¹ • x))) 1 volume = _
  rw [eLpNorm_const_smul, eLpNorm_dilate K hK 1 (inv_pos.mpr hh)]
  simp only [ENNReal.toReal_one, div_one, ENNReal.rpow_one, inv_pow, inv_inv]
  rw [Real.enorm_eq_ofReal (inv_nonneg.mpr (pow_nonneg hh.le n)), ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hh.le n))]
  simp [hh.ne']

theorem continuous_angularInverse {n : ℕ} {g : Space n → ℂ} (hg : Integrable g) :
    Continuous (OAI.Analysis.Fourier.LocalSmoothing.angularInverse g) := by
  change Continuous ((((2 * Real.pi) ^ n)⁻¹ : ℝ) •
    (fun x : Space n ↦ ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * g ξ))
  exact (continuous_positive_fourier_integral hg).const_smul _

theorem angularInverse_scaled_eq_waveKernel {n : ℕ} (φ : Space n → ℂ)
    {h : ℝ} (hh : 0 < h) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ φ (h • ξ)) x =
      (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ *
        OAI.Analysis.Fourier.WavePackets.semiclassicalWaveKernel volume φ h 0 x := by
  rw [← OAI.Analysis.Fourier.WavePackets.scaled_wave_integral φ hh 0 x]
  simp only [OAI.Analysis.Fourier.LocalSmoothing.angularInverse, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [OAI.Analysis.Fourier.WavePackets.oscillation, OAI.Analysis.Fourier.WavePackets.euclideanWavePhase, zero_mul, sub_zero, div_one]
  rw [mul_comm (inner ℝ x ξ : ℂ) Complex.I]

theorem frequencyHalfWave_zero_eq_convolution {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    {f : Space n → ℂ} (hf : Integrable f) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h 0 f x = OAI.Analysis.Fourier.WavePackets.complexConvolution
      (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ φ (h • ξ))) f volume x := by
  rw [OAI.Analysis.Fourier.WavePackets.frequencyHalfWave_eq_complexConvolution hφ hc hh 0 hf]
  simp only [OAI.Analysis.Fourier.WavePackets.complexConvolution, angularInverse_scaled_eq_waveKernel φ hh,
    mul_assoc, integral_const_mul]

theorem eLpNorm_angularInverse_dilate_one {n : ℕ} {φ : Space n → ℂ}
    (hφ : Integrable φ) {h : ℝ} (hh : 0 < h) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ φ (h • ξ))) 1 volume =
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ) 1 volume := by
  have heq : OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ φ (h • ξ)) =
      fun x ↦ (h ^ n)⁻¹ • OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ (h⁻¹ • x) :=
    funext (angularInverse_dilate φ hh)
  rw [heq]
  exact eLpNorm_normalized_dilate_one _ (continuous_angularInverse hφ).measurable hh

theorem eLpNorm_frequencyHalfWave_zero_le {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    {f : Space n → ℂ} (hf : Integrable f) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h 0 f) p volume ≤
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ) 1 volume * eLpNorm f p volume := by
  have hφint : Integrable φ := hφ.integrable_of_hasCompactSupport hc
  have hscaled : Integrable (fun ξ ↦ φ (h • ξ)) :=
    (hφ.comp (continuous_const.smul continuous_id)).integrable_of_hasCompactSupport
      (hc.comp_smul hh.ne')
  have heq : OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h 0 f = OAI.Analysis.Fourier.WavePackets.complexConvolution
      (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ φ (h • ξ))) f volume := by
    funext x
    exact frequencyHalfWave_zero_eq_convolution hφ hc hh hf x
  rw [heq, ← eLpNorm_angularInverse_dilate_one hφint hh]
  exact OAI.Analysis.Fourier.WavePackets.eLpNorm_complexConvolution_le
    (continuous_angularInverse hscaled).aestronglyMeasurable hf.aestronglyMeasurable hp hp_top

theorem uniform_angularInverse_L1 {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {n : ℕ} {K : Set Q} {S : Set (Space n)} (hK : IsCompact K) (hS : IsCompact S)
    {a : Q × Space n → ℂ} (ha : ContDiff ℝ ∞ a)
    (hs : tsupport a ⊆ Set.univ ×ˢ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K,
      Integrable (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ a (q, ξ))) ∧
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ a (q, ξ))) 1 volume ≤ ENNReal.ofReal C := by
  obtain ⟨B, hB, hb⟩ := uniform_fourier_integral_L1 hK hS ha hs
  let κ : ℝ := ((2 * Real.pi) ^ n)⁻¹
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  refine ⟨κ * B, mul_nonneg hκ hB, ?_⟩
  intro q hq
  obtain ⟨hi, hn⟩ := hb q hq
  refine ⟨hi.smul κ, ?_⟩
  change eLpNorm (κ • (fun x : Space n ↦ ∫ ξ,
    Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * a (q, ξ))) 1 volume ≤ _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hκ,
    eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hi, ENNReal.ofReal_mul hκ]
  gcongr

theorem uniform_frequencyHalfWave_zero_bound {Q : Type*} [NormedAddCommGroup Q]
    [NormedSpace ℝ Q] {n : ℕ} {K : Set Q} {S : Set (Space n)}
    (hK : IsCompact K) (hS : IsCompact S) {a : Q × Space n → ℂ}
    (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ Set.univ ×ˢ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ h : ℝ, 0 < h → ∀ f : Space n → ℂ,
      Integrable f → ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ ↦ a (q, ξ)) h 0 f) p volume ≤
        ENNReal.ofReal C * eLpNorm f p volume := by
  obtain ⟨C, hC, hc⟩ := uniform_angularInverse_L1 hK hS ha hs
  refine ⟨C, hC, ?_⟩
  intro q hq h hh f hf p hp hptop
  have hcont : Continuous (fun ξ ↦ a (q, ξ)) :=
    ha.continuous.comp (continuous_const.prodMk continuous_id)
  have hcompact : HasCompactSupport (fun ξ ↦ a (q, ξ)) := by
    apply hS.of_isClosed_subset (isClosed_tsupport _)
    intro ξ hξ
    exact (hs (tsupport_comp_subset_preimage a
      (continuous_const.prodMk continuous_id) hξ)).2
  exact (eLpNorm_frequencyHalfWave_zero_le hcont hcompact hh hf hp hptop).trans
    (mul_le_mul' (hc q hq).2 le_rfl)

end OAI.Analysis.Fourier.BochnerRiesz
