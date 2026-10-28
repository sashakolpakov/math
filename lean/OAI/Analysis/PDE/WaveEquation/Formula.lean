import OAI.Analysis.PDE.WaveEquation.PrimitiveFormula
import OAI.Analysis.PDE.WaveEquation.LowWeighted

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.PDE.WaveEquation

theorem angularInverse_const_mul {n : ℕ} (c : ℂ) (g : Space n → ℂ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ c * g ξ) x = c * OAI.Analysis.Fourier.LocalSmoothing.angularInverse g x := by
  simp only [OAI.Analysis.Fourier.LocalSmoothing.angularInverse, mul_left_comm (a := _) (b := c), integral_const_mul,
    mul_smul_comm]

theorem integrable_halfWave_symbol {n : ℕ} (f : SchwartzMap (Space n) ℂ) (t : ℝ) :
    Integrable (fun ξ ↦ Complex.exp (-Complex.I * (t*‖ξ‖:ℝ)) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) := by
  simpa using OAI.Analysis.Fourier.LocalSmoothing.integrable_wave_cutoff_symbol (χ := fun _ : Space n ↦ (1:ℂ))
    continuous_const (C := 1) (by intro ξ; simp) 1 t f

theorem waveDisplacement_eq_cosine {n : ℕ} (t : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    waveDisplacement t f x =
      OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ (Real.cos (t*‖ξ‖) : ℂ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) x := by
  have hadd := congrFun (OAI.Analysis.Fourier.WavePackets.angularInverse_add_integrable
    (integrable_halfWave_symbol f t) (integrable_halfWave_symbol f (-t))) x
  change OAI.Analysis.Fourier.LocalSmoothing.angularInverse _ x = OAI.Analysis.Fourier.LocalSmoothing.angularInverse _ x + OAI.Analysis.Fourier.LocalSmoothing.angularInverse _ x at hadd
  simp only [waveDisplacement,OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral]
  rw [← hadd, ← OAI.Analysis.Fourier.BochnerRiesz.angularInverse_smul_real]
  congr 1
  funext ξ
  simp only [Pi.add_apply,neg_mul]
  calc
    _ = ((1/2:ℝ) • (Complex.exp (-Complex.I * (t*‖ξ‖:ℝ)) +
        Complex.exp (-Complex.I * (-(t*‖ξ‖):ℝ)))) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ := by
      simp only [Complex.real_smul]
      ring_nf
    _ = _ := by rw [halfWave_cosine_scalar]

theorem waveHighVelocity_eq_sine {n : ℕ} (t : ℝ)
    (g : SchwartzMap (Space n) ℂ) (x : Space n) :
    waveHighVelocity t g x =
      OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ (Real.sin (t*‖ξ‖) : ℂ) *
        (velocityHighSymbol ξ : ℂ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ) x := by
  simp only [waveHighVelocity,OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral]
  rw [← OAI.Analysis.Fourier.LocalSmoothing.angularInverse_sub_of_integrable (integrable_halfWave_symbol (highVelocityData g) t)
    (integrable_halfWave_symbol (highVelocityData g) (-t)),
    ← OAI.Analysis.Fourier.BochnerRiesz.angularInverse_smul_real, ← angularInverse_const_mul]
  congr 1
  funext ξ
  rw [show OAI.Analysis.Fourier.LocalSmoothing.angularFourier (highVelocityData g) ξ =
      velocityHighSymbol ξ • OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ from
    OAI.Analysis.Fourier.BesselPotential.angularFourier_angularSchwartzMultiplier (temperate_velocityHighSymbol n) g ξ]
  simp only [neg_mul,Complex.real_smul]
  calc
    _ = (Complex.I * ((1/2:ℝ) • (Complex.exp (-Complex.I * (t*‖ξ‖:ℝ)) -
        Complex.exp (-Complex.I * (-(t*‖ξ‖):ℝ))))) *
          (velocityHighSymbol ξ : ℂ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ := by
      simp only [Complex.real_smul]
      ring_nf
    _ = _ := by rw [halfWave_sine_scalar]

theorem sine_high_multiplier {n : ℕ} (t : ℝ) (ξ : Space n) :
    Real.sin (t*‖ξ‖) * velocityHighSymbol ξ =
      t * Real.sinc (t*‖ξ‖) * (1-velocityLowCutoff ξ) := by
  rw [velocityHighSymbol_eq]
  by_cases ht : t = 0
  · simp [ht]
  by_cases hξ : ‖ξ‖ = 0
  · simp [hξ,velocityLowCutoff_one (show ‖ξ‖ ≤ 4 by rw [hξ]; norm_num)]
  rw [Real.sinc_of_ne_zero (mul_ne_zero ht hξ)]
  field_simp

/-- The removable sine-over-frequency propagator, with its true value at the origin. -/
def waveVelocity {n : ℕ} (t : ℝ) (g : Space n → ℂ) (x : Space n) : ℂ :=
  OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ ((t * Real.sinc (t*‖ξ‖):ℝ):ℂ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ) x

theorem waveVelocity_eq_high_add_low {n : ℕ} (t : ℝ)
    (g : SchwartzMap (Space n) ℂ) (x : Space n) :
    waveVelocity t g x = waveHighVelocity t g x + waveLowVelocity t g x := by
  let h : Space n → ℂ := fun ξ ↦ (Real.sin (t*‖ξ‖):ℂ) *
    (velocityHighSymbol ξ:ℂ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ
  have hh : Integrable h := by
    have he : h = fun ξ ↦ (Real.sin (t*‖ξ‖):ℂ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier (highVelocityData g) ξ := by
      funext ξ
      rw [show OAI.Analysis.Fourier.LocalSmoothing.angularFourier (highVelocityData g) ξ =
        velocityHighSymbol ξ • OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ from
        OAI.Analysis.Fourier.BesselPotential.angularFourier_angularSchwartzMultiplier (temperate_velocityHighSymbol n) g ξ]
      simp only [h,Complex.real_smul,mul_assoc]
    rw [he]
    apply (OAI.Analysis.Fourier.Restriction.integrable_angularFourier_schwartz (highVelocityData g)).norm.mono'
    · exact (by fun_prop : Continuous (fun ξ : Space n ↦ (Real.sin (t*‖ξ‖):ℂ))).aestronglyMeasurable.mul
        (OAI.Analysis.Fourier.Restriction.integrable_angularFourier_schwartz (highVelocityData g)).aestronglyMeasurable
    · filter_upwards [] with ξ
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)
  let l : Space n → ℂ := fun ξ ↦ ((t*Real.sinc (t*‖ξ‖):ℝ):ℂ) *
    (velocityLowCutoff ξ:ℂ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ
  have hlc : Continuous l := by
    have hs : Continuous (fun ξ : Space n ↦ Real.sinc (t*‖ξ‖)) :=
      Real.continuous_sinc.comp (by fun_prop)
    exact ((Complex.ofRealCLM.continuous.comp (continuous_const.mul hs)).mul
      (contDiff_complex_velocityLowCutoff n).continuous).mul
      (OAI.Analysis.Fourier.Restriction.continuous_angularFourier g.integrable)
  have hl : Integrable l := hlc.integrable_of_hasCompactSupport
    (((hasCompactSupport_complex_velocityLowCutoff n).mul_left).mul_right)
  rw [waveHighVelocity_eq_sine]
  change _ = OAI.Analysis.Fourier.LocalSmoothing.angularInverse h x + frequencyWavePrimitive
    (fun ξ ↦ (velocityLowCutoff ξ:ℂ)) t g x
  rw [frequencyWavePrimitive_eq_sinc (contDiff_complex_velocityLowCutoff n)
    (hasCompactSupport_complex_velocityLowCutoff n)]
  change _ = OAI.Analysis.Fourier.LocalSmoothing.angularInverse h x + OAI.Analysis.Fourier.LocalSmoothing.angularInverse l x
  have hadd := congrFun (OAI.Analysis.Fourier.WavePackets.angularInverse_add_integrable hh hl) x
  change OAI.Analysis.Fourier.LocalSmoothing.angularInverse _ x = OAI.Analysis.Fourier.LocalSmoothing.angularInverse h x + OAI.Analysis.Fourier.LocalSmoothing.angularInverse l x at hadd
  rw [← hadd]
  unfold waveVelocity
  congr 1
  funext ξ
  simp only [h,l,Pi.add_apply]
  rw [← Complex.ofReal_mul, sine_high_multiplier]
  simp only [Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one]
  ring

end OAI.Analysis.PDE.WaveEquation
