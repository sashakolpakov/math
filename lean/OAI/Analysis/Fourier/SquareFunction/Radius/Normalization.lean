import OAI.Analysis.Fourier.SquareFunction.Radius.FTC
import OAI.Analysis.Fourier.Restriction.FourierProduct

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology
namespace OAI.Analysis.Fourier.SquareFunction

def bochnerRieszFrequencyIntegrand {n : ℕ} (f : Space n → ℂ) (x ξ : Space n) : ℂ :=
  Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ

theorem continuous_bochnerRieszFrequencyIntegrand {n : ℕ}
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Continuous (bochnerRieszFrequencyIntegrand f x) := by
  have hF := OAI.Analysis.Fourier.Restriction.continuous_angularFourier f.integrable
  unfold bochnerRieszFrequencyIntegrand
  fun_prop

theorem norm_bochnerRieszFrequencyIntegrand {n : ℕ}
    (f : Space n → ℂ) (x ξ : Space n) :
    ‖bochnerRieszFrequencyIntegrand f x ξ‖ = ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ‖ := by
  simp [bochnerRieszFrequencyIntegrand, Complex.norm_exp]

theorem integrable_bochnerRieszFrequencyIntegrand {n : ℕ}
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Integrable (bochnerRieszFrequencyIntegrand f x) :=
  (OAI.Analysis.Fourier.Restriction.integrable_angularFourier_schwartz f).norm.mono'
    (continuous_bochnerRieszFrequencyIntegrand f x).aestronglyMeasurable
    (Eventually.of_forall (fun ξ => le_of_eq (norm_bochnerRieszFrequencyIntegrand f x ξ)))

theorem bochnerRiesz_eq_radiusPowerIntegral {n : ℕ} (α r : ℝ)
    (f : Space n → ℂ) (x : Space n) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz α r f x = (((2 * Real.pi)^n)⁻¹ : ℝ) •
      OAI.Analysis.Fourier.SquareFunction.radiusPowerIntegral α (bochnerRieszFrequencyIntegrand f x) r := by
  unfold OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz OAI.Analysis.Fourier.LocalSmoothing.angularInverse OAI.Analysis.Fourier.SquareFunction.radiusPowerIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol, OAI.Analysis.Fourier.SquareFunction.radiusPower, bochnerRieszFrequencyIntegrand,
    Complex.real_smul]
  ring

theorem radiusDerivative_eq_radiusPowerIntegralDerivative {n : ℕ}
    (α r : ℝ) (f : Space n → ℂ) (x : Space n) :
    r⁻¹ • OAI.Analysis.Fourier.SquareFunction.radiusDerivative α r f x = (((2 * Real.pi)^n)⁻¹ : ℝ) •
      OAI.Analysis.Fourier.SquareFunction.radiusPowerIntegralDerivative α (bochnerRieszFrequencyIntegrand f x) r := by
  unfold OAI.Analysis.Fourier.SquareFunction.radiusDerivative OAI.Analysis.Fourier.LocalSmoothing.angularInverse OAI.Analysis.Fourier.SquareFunction.radiusPowerIntegralDerivative
  rw [smul_comm (r⁻¹), ← integral_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [OAI.Analysis.Fourier.SquareFunction.radiusPowerDerivative, OAI.Analysis.Fourier.SquareFunction.radiusDerivativeSymbol, OAI.Analysis.Fourier.SquareFunction.radiusMultiplier,
    bochnerRieszFrequencyIntegrand, Complex.real_smul, Complex.ofReal_mul]
  ring

end OAI.Analysis.Fourier.SquareFunction
