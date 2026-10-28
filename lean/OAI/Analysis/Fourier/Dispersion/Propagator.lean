import OAI.Analysis.Fourier.Dispersion.Scaling
import OAI.Analysis.Fourier.WavePackets.WaveDataLowTime

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology
noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

def dispersionIntegral {n : ℕ} (disp : Space n → ℝ) (t : ℝ)
    (f : Space n → ℂ) (x : Space n) : ℂ :=
  OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ Complex.exp (-Complex.I * (t*disp ξ:ℝ)) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) x

def massiveHalfWave {n : ℕ} (m t : ℝ) (f : Space n → ℂ) (x : Space n) : ℂ :=
  dispersionIntegral (fun ξ ↦ Real.sqrt (m^2+‖ξ‖^2)) t f x

theorem continuous_dispersionIntegral {n : ℕ} {disp : Space n → ℝ} (hd : Continuous disp)
    (f : SchwartzMap (Space n) ℂ) :
    Continuous (fun z : Space n × ℝ ↦ dispersionIntegral disp z.2 f z.1) := by
  have hF := OAI.Analysis.Fourier.Restriction.integrable_angularFourier_schwartz f
  have hFc := OAI.Analysis.Fourier.Restriction.continuous_angularFourier f.integrable
  let H : (Space n × ℝ) → Space n → ℂ := fun z ξ ↦
    Complex.exp (Complex.I*(inner ℝ z.1 ξ:ℂ)) *
      (Complex.exp (-Complex.I*(z.2*disp ξ:ℝ))*OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ)
  have hc : Continuous (fun z : Space n × ℝ ↦ ∫ ξ,H z ξ) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply tendsto_integral_filter_of_dominated_convergence (fun ξ ↦ ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ‖)
    · apply Filter.Eventually.of_forall
      intro y
      exact (by dsimp only [H]; fun_prop : Continuous (H y)).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro y
      exact Filter.Eventually.of_forall fun ξ ↦ by simp [H,Complex.norm_exp]
    · exact hF.norm
    · exact Filter.Eventually.of_forall fun ξ ↦
        (by dsimp only [H]; fun_prop : Continuous (fun y : Space n × ℝ ↦ H y ξ)).tendsto z
  exact hc.const_smul (((2*Real.pi)^n)⁻¹ : ℝ)

theorem continuous_massiveHalfWave {n : ℕ} (m : ℝ) (f : SchwartzMap (Space n) ℂ) :
    Continuous (fun z : Space n × ℝ ↦ massiveHalfWave m z.2 f z.1) :=
  continuous_dispersionIntegral (by fun_prop) f

theorem massiveHalfWave_zero {n : ℕ} (t : ℝ) (f : Space n → ℂ) (x : Space n) :
    massiveHalfWave 0 t f x = OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x := by
  simp only [massiveHalfWave,dispersionIntegral,OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral,zero_pow (by omega : 2≠0),
    zero_add,Real.sqrt_sq (norm_nonneg _)]

def velocityLowData {n : ℕ} (f : SchwartzMap (Space n) ℂ) : SchwartzMap (Space n) ℂ :=
  OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier OAI.Analysis.PDE.WaveEquation.velocityLowCutoff f

theorem halfWave_velocityLowData {n : ℕ} (t : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t (velocityLowData f) x =
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ ↦ (OAI.Analysis.PDE.WaveEquation.velocityLowCutoff ξ:ℂ)) 1 t f x := by
  simp only [OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral,OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave,velocityLowData,
    OAI.Analysis.Fourier.BesselPotential.angularFourier_angularSchwartzMultiplier (OAI.Analysis.PDE.WaveEquation.temperate_velocityLowCutoff n),
    Complex.real_smul,one_smul,mul_assoc]

def smoothHighWaveSymbol {n : ℕ} (t : ℝ) (ξ : Space n) : ℂ :=
  Complex.exp (-Complex.I*(t*regularizedRadius ξ:ℝ)) * (1-OAI.Analysis.PDE.WaveEquation.velocityLowCutoff ξ:ℝ)

theorem temperate_smoothHighWaveSymbol (n : ℕ) (t : ℝ) :
    (smoothHighWaveSymbol (n := n) t).HasTemperateGrowth := by
  have hp := Complex.hasTemperateGrowth_exp_mul_I.comp
    ((Function.HasTemperateGrowth.const (-t)).mul (temperate_regularizedRadius n))
  have he : (fun ξ : Space n ↦ Complex.exp (-Complex.I*(t*regularizedRadius ξ:ℝ))) =
      fun ξ ↦ Complex.exp ((-t*regularizedRadius ξ:ℝ)*Complex.I) := by
    funext ξ
    congr 1
    push_cast
    ring
  have hp' : (fun ξ : Space n ↦ Complex.exp (-Complex.I*(t*regularizedRadius ξ:ℝ))).HasTemperateGrowth := by
    rw [he]
    exact hp
  exact hp'.mul (Complex.ofRealCLM.hasTemperateGrowth.comp
    ((Function.HasTemperateGrowth.const 1).sub (OAI.Analysis.PDE.WaveEquation.temperate_velocityLowCutoff n)))

theorem smoothHighWaveSymbol_eq {n : ℕ} (t : ℝ) (ξ : Space n) :
    smoothHighWaveSymbol t ξ = Complex.exp (-Complex.I*(t*‖ξ‖:ℝ)) *
      (1-OAI.Analysis.PDE.WaveEquation.velocityLowCutoff ξ:ℝ) := by
  by_cases h : ‖ξ‖ ≤ 4
  · simp [smoothHighWaveSymbol,OAI.Analysis.PDE.WaveEquation.velocityLowCutoff_one h]
  · rw [smoothHighWaveSymbol,regularizedRadius,OAI.Analysis.PDE.WaveEquation.velocityRadiusSq_eq (le_of_not_ge h),
      Real.sqrt_sq (norm_nonneg ξ)]

def smoothHighWave {n : ℕ} (t : ℝ) (f : SchwartzMap (Space n) ℂ) : SchwartzMap (Space n) ℂ :=
  complexAngularSchwartzMultiplier (smoothHighWaveSymbol t) f

theorem smoothHighWave_eq_sub {n : ℕ} (t : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    smoothHighWave t f x = OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x - OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t (velocityLowData f) x := by
  rw [smoothHighWave,complexAngularSchwartzMultiplier_eq_integral (temperate_smoothHighWaveSymbol n t)]
  simp only [OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral]
  rw [← OAI.Analysis.Fourier.LocalSmoothing.angularInverse_sub_of_integrable (OAI.Analysis.PDE.WaveEquation.integrable_halfWave_symbol f t)
    (OAI.Analysis.PDE.WaveEquation.integrable_halfWave_symbol (velocityLowData f) t)]
  congr 1
  funext ξ
  rw [smoothHighWaveSymbol_eq]
  simp only [velocityLowData,OAI.Analysis.Fourier.BesselPotential.angularFourier_angularSchwartzMultiplier (OAI.Analysis.PDE.WaveEquation.temperate_velocityLowCutoff n),
    Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_one]
  ring

theorem massiveCorrection_mul_high {n : ℕ} (m t : ℝ) (ξ : Space n) :
    massiveCorrection m t ξ * smoothHighWaveSymbol t ξ =
      Complex.exp (-Complex.I*(t*Real.sqrt (m^2+‖ξ‖^2):ℝ)) * (1-OAI.Analysis.PDE.WaveEquation.velocityLowCutoff ξ:ℝ) := by
  by_cases h : ‖ξ‖ ≤ 4
  · simp [smoothHighWaveSymbol,OAI.Analysis.PDE.WaveEquation.velocityLowCutoff_one h]
  · rw [massiveCorrection,smoothHighWaveSymbol,← mul_assoc (Complex.exp _) (Complex.exp _),
      ← Complex.exp_add,regularizedRadius,OAI.Analysis.PDE.WaveEquation.velocityRadiusSq_eq (le_of_not_ge h),
      Real.sqrt_sq (norm_nonneg ξ)]
    congr 2
    push_cast
    ring

theorem massiveCorrection_high_eq_sub {n : ℕ} (m t : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    complexAngularSchwartzMultiplier (massiveCorrection m t) (smoothHighWave t f) x =
      massiveHalfWave m t f x - massiveHalfWave m t (velocityLowData f) x := by
  rw [complexAngularSchwartzMultiplier_eq_integral (temperate_massiveCorrection n m t)]
  have hi (g : SchwartzMap (Space n) ℂ) : Integrable (fun ξ ↦
      Complex.exp (-Complex.I*(t*Real.sqrt (m^2+‖ξ‖^2):ℝ))*OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ) := by
    apply (OAI.Analysis.Fourier.Restriction.integrable_angularFourier_schwartz g).norm.mono'
    · have hc : Continuous (fun ξ : Space n ↦
        Complex.exp (-Complex.I*(t*Real.sqrt (m^2+‖ξ‖^2):ℝ))) := by fun_prop
      exact hc.aestronglyMeasurable.mul
        (OAI.Analysis.Fourier.Restriction.integrable_angularFourier_schwartz g).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ξ ↦ by simp [Complex.norm_exp]
  simp only [massiveHalfWave,dispersionIntegral]
  rw [← OAI.Analysis.Fourier.LocalSmoothing.angularInverse_sub_of_integrable (hi f) (hi (velocityLowData f))]
  congr 1
  funext ξ
  rw [show OAI.Analysis.Fourier.LocalSmoothing.angularFourier (smoothHighWave t f) ξ =
      smoothHighWaveSymbol t ξ * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ from
    angularFourier_complexAngularSchwartzMultiplier (temperate_smoothHighWaveSymbol n t) f ξ,
    ← mul_assoc,massiveCorrection_mul_high]
  simp only [velocityLowData,OAI.Analysis.Fourier.BesselPotential.angularFourier_angularSchwartzMultiplier (OAI.Analysis.PDE.WaveEquation.temperate_velocityLowCutoff n),
    Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_one]
  ring

end OAI.Analysis.Fourier.Dispersion
