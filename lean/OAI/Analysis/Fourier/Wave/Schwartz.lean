import OAI.Analysis.Fourier.Wave.AngularTransform
import OAI.Analysis.Fourier.Wave.Compatibility
import OAI.Analysis.Fourier.Wave.Continuity

open _root_.MeasureTheory FourierTransform
noncomputable section
namespace OAI.Analysis.Fourier.Wave

theorem integrable_wavePhase_mul {n : ℕ} (t : ℝ) (g : Space n → ℂ)
    (hg : Integrable g) : Integrable (fun ξ ↦ wavePhase t ξ * g ξ) := by
  have hm : AEStronglyMeasurable (fun ξ : Space n ↦ wavePhase t ξ * g ξ)
      (volume : Measure (Space n)) :=
    (continuous_wavePhase t).aestronglyMeasurable.mul hg.aestronglyMeasurable
  rw [← integrable_norm_iff hm]
  simpa only [norm_mul, norm_wavePhase, one_mul] using hg.norm

/-- The classical half-wave integral on Schwartz data agrees with the unitary
L² propagator, with the exact angular-frequency normalization of the source. -/
theorem halfWaveL2_schwartz_coe {n : ℕ} (t : ℝ) (f : SchwartzMap (Space n) ℂ) :
    (fun x ↦ halfWaveL2 t (f.toLp 2) x) =ᵐ[volume] OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f := by
  have hF : (Lp.fourierTransformₗᵢ (Space n) ℂ) (f.toLp 2) = (𝓕 f).toLp 2 := by
    change 𝓕 (f.toLp 2) = (𝓕 f).toLp 2
    exact SchwartzMap.toLp_fourier_eq f
  let g : WaveL2 n := phaseMultiply t ((𝓕 f).toLp 2)
  have hcoe : (g : Space n → ℂ) =ᵐ[volume]
      fun ξ ↦ wavePhase t ξ * (𝓕 f) ξ := by
    filter_upwards [phaseMultiply_coe t ((𝓕 f).toLp 2),
      (𝓕 f).coeFn_toLp 2 volume] with ξ h₁ h₂
    dsimp only [g]
    rw [h₁, h₂]
  have hg : Integrable (g : Space n → ℂ) :=
    (integrable_wavePhase_mul t (⇑(𝓕 f : SchwartzMap (Space n) ℂ))
      (𝓕 f).integrable).congr hcoe.symm
  have hInv := inverseFourierL2_coe g hg
  have heq : halfWaveL2 t (f.toLp 2) =
      (Lp.fourierTransformₗᵢ (Space n) ℂ).symm g := by
    simp only [halfWaveL2, hF, g]
  rw [heq, halfWaveIntegral_eq_fourierInv]
  filter_upwards [hInv] with x hx
  rw [hx, Real.fourierInv_congr_ae hcoe x]
  simp only [SchwartzMap.fourier_coe]

theorem memLp_halfWaveIntegral_two {n : ℕ} (t : ℝ) (f : SchwartzMap (Space n) ℂ) :
    MemLp (OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f) 2 := by
  let u : WaveL2 n := halfWaveL2 t (f.toLp 2 volume)
  have hcoe : (u : Space n → ℂ) =ᵐ[volume] OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f :=
    halfWaveL2_schwartz_coe t f
  exact (memLp_congr_ae (p := (2 : ENNReal)) hcoe).mp (Lp.memLp u)

theorem halfWaveIntegral_energy {n : ℕ} (t : ℝ) (f : SchwartzMap (Space n) ℂ) :
    (∫ x, ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  let f₂ : WaveL2 n := f.toLp 2 volume
  let u₂ : WaveL2 n := halfWaveL2 t f₂
  have hcoe : (fun x : Space n ↦ u₂ x) =ᵐ[volume] OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f :=
    halfWaveL2_schwartz_coe t f
  calc
    (∫ x, ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ ^ 2) =
        ∫ x, ‖u₂ x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hcoe] with x hx
      rw [hx]
    _ = ‖u₂‖ ^ 2 := (waveL2_norm_sq_integral u₂).symm
    _ = ‖f₂‖ ^ 2 := by simp only [u₂, norm_halfWaveL2]
    _ = ∫ x, ‖f₂ x‖ ^ 2 := waveL2_norm_sq_integral f₂
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [f.coeFn_toLp 2 volume] with x hx
      rw [hx]

end OAI.Analysis.Fourier.Wave
