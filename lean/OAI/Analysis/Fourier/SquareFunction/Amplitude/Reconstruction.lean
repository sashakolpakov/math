import OAI.Analysis.Fourier.SquareFunction.Amplitude.Separation

open OAI.Analysis.Fourier.Wave

/-! Fubini reconstruction of the actual radius-dependent shell operator. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform
open scoped ENNReal ContDiff

noncomputable def separatedShellIntegrand {n : ℕ} (A : ℝ × Space n → ℂ)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n)
    (z : ℝ × Space n) : C(RadiusInterval, ℂ) :=
  spatialPhase x z.2 • (𝓕 (f : Space n → ℂ) z.2 • separatedAmplitudeSymbol A φ δ z.1 z.2)

theorem continuous_separatedShellIntegrand {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Continuous (separatedShellIntegrand A φ δ f x) :=
  ((continuous_spatialPhase x).comp continuous_snd).smul
    (((𝓕 f).continuous.comp continuous_snd).smul
      (continuous_separatedAmplitudeSymbol hA hc φ δ))

theorem norm_separatedShellIntegrand_le {n : ℕ} (A : ℝ × Space n → ℂ)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n)
    (z : ℝ × Space n) {C : ℝ}
    (hC : ‖OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A z.1 z.2‖ ≤ C * (1 + |z.1|) ^ (-2 : ℝ)) :
    ‖separatedShellIntegrand A φ δ f x z‖ ≤
      (C * (1 + |z.1|) ^ (-2 : ℝ)) * (SchwartzMap.seminorm ℝ 0 0 φ * ‖(𝓕 f) z.2‖) := by
  simp only [separatedShellIntegrand, norm_smul, norm_spatialPhase, one_mul]
  calc
    _ ≤ ‖𝓕 (f : Space n → ℂ) z.2‖ *
        (‖OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A z.1 z.2‖ * SchwartzMap.seminorm ℝ 0 0 φ) :=
      mul_le_mul_of_nonneg_left (norm_separatedAmplitudeSymbol_le A φ δ z.1 z.2) (norm_nonneg _)
    _ ≤ ‖𝓕 (f : Space n → ℂ) z.2‖ *
        ((C * (1 + |z.1|) ^ (-2 : ℝ)) * SchwartzMap.seminorm ℝ 0 0 φ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC (apply_nonneg _ _)) (norm_nonneg _)
    _ = _ := by rw [SchwartzMap.fourier_coe]; ring

theorem integrable_separatedShellIntegrand {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Integrable (separatedShellIntegrand A φ δ f x) (volume.prod volume) := by
  obtain ⟨C, hC, hb⟩ := amplitudeInput_bound hA hc
  apply ((integrable_separation_weight.const_mul C).mul_prod
    ((𝓕 f).integrable.norm.const_mul (SchwartzMap.seminorm ℝ 0 0 φ))).mono'
      (continuous_separatedShellIntegrand hA hc φ δ f x).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => norm_separatedShellIntegrand_le A φ δ f x z ((hb z.1).1 z.2)

theorem integrable_separatedShellIntegrand_slice {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) (η : ℝ) :
    Integrable (fun ξ => separatedShellIntegrand A φ δ f x (η, ξ)) := by
  obtain ⟨C, hC, hb⟩ := amplitudeInput_bound hA hc
  have hf : Integrable (fun ξ : Space n => ‖(𝓕 f) ξ‖) volume := (𝓕 f).integrable.norm
  apply ((hf.const_mul (SchwartzMap.seminorm ℝ 0 0 φ)).const_mul
    (C * (1 + |η|) ^ (-2 : ℝ))).mono'
      ((continuous_separatedShellIntegrand hA hc φ δ f x).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => norm_separatedShellIntegrand_le A φ δ f x (η, ξ) ((hb η).1 ξ)

theorem integral_separatedShellIntegrand_radius {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x ξ : Space n) :
    (∫ η : ℝ, separatedShellIntegrand A φ δ f x (η, ξ)) =
      spatialPhase x ξ • (𝓕 (f : Space n → ℂ) ξ • amplitudeShellSymbol A hA.continuous φ δ ξ) := by
  simp only [separatedShellIntegrand, integral_smul,
    integral_separatedAmplitudeSymbol hA hc φ δ ξ]

theorem integral_separatedShellIntegrand_space {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) (η : ℝ) :
    (∫ ξ : Space n, separatedShellIntegrand A φ δ f x (η, ξ)) =
      radiusModulation η * thinShellRadiusMap φ δ (amplitudeInput A η f) x := by
  ext r
  rw [ContinuousMap.integral_apply (integrable_separatedShellIntegrand_slice hA hc φ δ f x η)]
  change (∫ ξ : Space n, spatialPhase x ξ * (𝓕 (f : Space n → ℂ) ξ *
      (OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A η ξ * (radiusModulation η r * φ (((r : ℝ) - ‖ξ‖) / δ))))) =
    radiusModulation η r * thinShellCycles φ δ (amplitudeInput A η f) x r
  unfold thinShellCycles
  rw [fourierInv_eq_spatialPhase_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [smul_eq_mul, fourier_amplitudeInput hA hc η f ξ, SchwartzMap.fourier_coe]
  ring

theorem amplitudeShellRadiusMap_eq_integral {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    amplitudeShellRadiusMap A hA.continuous φ δ f x =
      ∫ η : ℝ, radiusModulation η * thinShellRadiusMap φ δ (amplitudeInput A η f) x := by
  rw [amplitudeShellRadiusMap, fourierInv_eq_spatialPhase_smul]
  trans ∫ ξ : Space n, ∫ η : ℝ, separatedShellIntegrand A φ δ f x (η, ξ)
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ => (integral_separatedShellIntegrand_radius hA hc φ δ f x ξ).symm
  · rw [integral_integral_swap
      (f := fun ξ η => separatedShellIntegrand A φ δ f x (η, ξ))
      (integrable_separatedShellIntegrand hA hc φ δ f x).swap]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (integral_separatedShellIntegrand_space hA hc φ δ f x)

noncomputable def separatedShellOutput {n : ℕ} (A : ℝ × Space n → ℂ)
    (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (f : SchwartzMap (Space n) ℂ)
    (z : Space n × ℝ) : C(RadiusInterval, ℂ) :=
  radiusModulation z.2 * thinShellRadiusMap φ δ (amplitudeInput A z.2 f) z.1

theorem integrable_separatedShellOutput {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Integrable (fun η => separatedShellOutput A φ δ f (x, η)) := by
  have h := (integrable_separatedShellIntegrand hA hc φ δ f x).integral_prod_left
  simpa only [separatedShellOutput, integral_separatedShellIntegrand_space hA hc φ δ f x] using h

theorem amplitudeShellHilbert_eq_integral {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    amplitudeShellHilbert A hA.continuous φ δ f x =
      ∫ η : ℝ, radiusToL2 (separatedShellOutput A φ δ f (x, η)) := by
  rw [amplitudeShellHilbert, amplitudeShellRadiusMap_eq_integral hA hc]
  exact (radiusToL2.integral_comp_comm (integrable_separatedShellOutput hA hc φ δ f x)).symm

theorem enorm_amplitudeShellHilbert_le {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    ‖amplitudeShellHilbert A hA.continuous φ δ f x‖ₑ ≤
      ∫⁻ η : ℝ, ‖thinShellHilbert φ δ (amplitudeInput A η f) x‖ₑ := by
  rw [amplitudeShellHilbert_eq_integral hA hc]
  apply (enorm_integral_le_lintegral_enorm _).trans_eq
  apply lintegral_congr
  intro η
  exact enorm_radiusToL2_modulation η _

end OAI.Analysis.Fourier.SquareFunction
