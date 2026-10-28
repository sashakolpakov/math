import OAI.Analysis.Fourier.LocalSmoothing.Definitions
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open _root_.MeasureTheory FourierTransform
noncomputable section
namespace OAI.Analysis.Fourier.Wave

/-- Conversion of the manuscript's angular-frequency transform to the
cycles-per-unit convention used by Mathlib. -/
theorem angularFourier_scaled {n : ℕ} (f : Space n → ℂ) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ((2 * Real.pi) • ξ) = 𝓕 f ξ := by
  rw [OAI.Analysis.Fourier.LocalSmoothing.angularFourier, Real.fourier_eq']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    simp only [inner_smul_right, Complex.ofReal_mul, Complex.ofReal_neg, smul_eq_mul]
    congr 2
    push_cast
    ring

/-- Exact Jacobian cancellation in the angular-frequency inverse transform. -/
theorem angularInverse_eq_fourierInv_scaled {n : ℕ} (g : Space n → ℂ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse g x = 𝓕⁻ (fun ξ ↦ g ((2 * Real.pi) • ξ)) x := by
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  have hchange := Measure.integral_comp_smul_of_nonneg (volume : Measure (Space n))
    (fun ξ ↦ Complex.exp (Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) * g ξ)
    (2 * Real.pi) (hR := hπ)
  calc
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse g x =
      ∫ ξ, Complex.exp (Complex.I * ((inner ℝ x ((2 * Real.pi) • ξ) : ℝ) : ℂ)) *
        g ((2 * Real.pi) • ξ) := by
      simpa [OAI.Analysis.Fourier.LocalSmoothing.angularInverse, Space] using hchange.symm
    _ = 𝓕⁻ (fun ξ ↦ g ((2 * Real.pi) • ξ)) x := by
      rw [Real.fourierInv_eq']
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ ↦ by
        simp only [inner_smul_right, real_inner_comm x ξ, Complex.ofReal_mul, smul_eq_mul]
        congr 2
        push_cast
        ring

/-- The pointwise oscillatory integral and the L² flow use the same symbol. -/
theorem halfWaveIntegral_eq_fourierInv {n : ℕ} (t : ℝ) (f : Space n → ℂ) :
    OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f = 𝓕⁻ (fun ξ ↦ wavePhase t ξ * 𝓕 f ξ) := by
  funext x
  rw [OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral, angularInverse_eq_fourierInv_scaled]
  rw [Real.fourierInv_eq', Real.fourierInv_eq']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ ↦ by
    have hphase : Complex.exp (-Complex.I * (t * ‖(2 * Real.pi) • ξ‖ : ℝ)) =
        wavePhase t ξ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      unfold wavePhase
      congr 1
      push_cast
      ring
    dsimp only
    rw [hphase, angularFourier_scaled]

end OAI.Analysis.Fourier.Wave
