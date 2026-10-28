import OAI.Analysis.Fourier.Wave.Schwartz

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing

@[simp] theorem smoothingOrder_two (n : ℕ) : smoothingOrder n 2 = 0 := by
  unfold smoothingOrder
  have h : ((n : ℝ) - 1) / 2 - n / 2 = -(1 / 2 : ℝ) := by ring
  rw [h]
  norm_num

@[simp] theorem besselPotential_zero {n : ℕ} (f : SchwartzMap (Space n) ℂ) :
    besselPotential 0 f = f := by
  have hF : Integrable (𝓕 (f : Space n → ℂ)) := by
    simpa only [← SchwartzMap.fourier_coe] using (𝓕 f).integrable
  funext x
  simp only [besselPotential, zero_div, Real.rpow_zero, one_smul]
  rw [OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled]
  simp_rw [OAI.Analysis.Fourier.Wave.angularFourier_scaled]
  exact f.integrable.fourierInv_fourier_eq hF f.continuous.continuousAt

/-- Joint continuity of the classical half-wave solution for Schwartz data. -/
theorem continuous_halfWaveIntegral {n : ℕ} (f : SchwartzMap (Space n) ℂ) :
    Continuous (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) := by
  let F : (Space n × ℝ) → Space n → ℂ := fun z ξ ↦
    Complex.exp (((2 * Real.pi * inner ℝ ξ z.1 : ℝ) : ℂ) * Complex.I) *
      OAI.Analysis.Fourier.Wave.wavePhase z.2 ξ * (𝓕 f) ξ
  have hrep : (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) =
      fun z ↦ ∫ ξ, F z ξ := by
    funext z
    rw [OAI.Analysis.Fourier.Wave.halfWaveIntegral_eq_fourierInv, Real.fourierInv_eq']
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ ↦ by
      simp only [F, smul_eq_mul, mul_assoc, SchwartzMap.fourier_coe]
  rw [hrep]
  apply continuous_of_dominated (bound := fun ξ ↦ ‖(𝓕 f) ξ‖)
  · intro z
    have hleft : Continuous (fun ξ : Space n ↦
        Complex.exp (((2 * Real.pi * inner ℝ ξ z.1 : ℝ) : ℂ) * Complex.I) *
          OAI.Analysis.Fourier.Wave.wavePhase z.2 ξ) := by
      unfold OAI.Analysis.Fourier.Wave.wavePhase
      fun_prop
    exact (hleft.mul (𝓕 f).continuous).aestronglyMeasurable
  · intro z
    exact Filter.Eventually.of_forall fun ξ ↦ by
      simp [F, Complex.norm_exp]
  · exact (𝓕 f).integrable.norm
  · exact Filter.Eventually.of_forall fun ξ ↦ by
      unfold F OAI.Analysis.Fourier.Wave.wavePhase
      fun_prop

/-- Square-integrability in physical space and time, without derivative loss. -/
theorem memLp_halfWaveIntegral_spacetime_two {n : ℕ} (f : SchwartzMap (Space n) ℂ) :
    MemLp (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) 2
      (observationMeasure n) := by
  have hm : AEStronglyMeasurable
      (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) (observationMeasure n) :=
    (continuous_halfWaveIntegral f).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hsq : AEStronglyMeasurable
      (fun z : Space n × ℝ ↦ ‖halfWaveIntegral z.2 f z.1‖ ^ 2) (observationMeasure n) :=
    ((continuous_halfWaveIntegral f).norm.pow 2).aestronglyMeasurable
  apply (integrable_prod_iff' hsq).mpr
  constructor
  · exact Filter.Eventually.of_forall fun t ↦
      (memLp_two_iff_integrable_sq_norm
        ((continuous_halfWaveIntegral f).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable).mp
        (OAI.Analysis.Fourier.Wave.memLp_halfWaveIntegral_two t f)
  · simp only [norm_pow, norm_norm, OAI.Analysis.Fourier.Wave.halfWaveIntegral_energy]
    exact integrable_const _

/-- Exact conservation of energy on the unit-length observation interval. -/
theorem halfWaveIntegral_spacetime_energy {n : ℕ} (f : SchwartzMap (Space n) ℂ) :
    (∫ z : Space n × ℝ, ‖halfWaveIntegral z.2 f z.1‖ ^ 2 ∂observationMeasure n) =
      ∫ x, ‖f x‖ ^ 2 := by
  have hsq := (memLp_two_iff_integrable_sq_norm
    ((continuous_halfWaveIntegral f).aestronglyMeasurable :
      AEStronglyMeasurable (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1)
        (observationMeasure n))).mp (memLp_halfWaveIntegral_spacetime_two f)
  rw [observationMeasure, integral_prod_symm _ hsq]
  simp only [OAI.Analysis.Fourier.Wave.halfWaveIntegral_energy, integral_const]
  norm_num [Measure.real, Real.volume_Icc]

/-- The zero-loss p=2 local-smoothing identity for the source's actual
oscillatory integral and product-space norm. -/
theorem halfWaveIntegral_spacetime_eLpNorm_two {n : ℕ} (f : SchwartzMap (Space n) ℂ) :
    eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) 2 (observationMeasure n) =
      eLpNorm f 2 volume := by
  rw [(memLp_halfWaveIntegral_spacetime_two f).eLpNorm_eq_integral_rpow_norm
      (by norm_num) (by norm_num),
    (f.memLp 2 volume).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [halfWaveIntegral_spacetime_energy]

/-- The p=2, ε=0 branch of the main theorem, with constant exactly one. -/
theorem localSmoothing_two {n : ℕ} (f : SchwartzMap (Space n) ℂ) :
    MemLp (besselPotential (smoothingOrder n 2) f) 2 volume ∧
    MemLp (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) 2 (observationMeasure n) ∧
    eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) 2 (observationMeasure n) ≤
      eLpNorm (besselPotential (smoothingOrder n 2) f) 2 volume := by
  simp only [smoothingOrder_two, besselPotential_zero]
  exact ⟨f.memLp 2 volume, memLp_halfWaveIntegral_spacetime_two f,
    (halfWaveIntegral_spacetime_eLpNorm_two f).le⟩

end OAI.Analysis.Fourier.LocalSmoothing
