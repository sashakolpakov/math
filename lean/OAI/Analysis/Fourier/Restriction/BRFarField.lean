import OAI.Analysis.Fourier.Restriction.TwoRadiusNorm
import OAI.Analysis.Fourier.Restriction.RateAlgebra
import OAI.Analysis.Fourier.BochnerRiesz.CompactInput

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- The two-radius extraction for the actual Bochner--Riesz kernel. -/
theorem bochnerRiesz_farField_norm {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c D : ℝ, 0 < c ∧ 0 ≤ D ∧ ∀ R : ℝ, 0 ≤ R → ∀ f : Space n → ℂ,
      Measurable f → Integrable f → (∀ y, R < ‖y‖ → f y = 0) →
      ∀ p T : ℝ, 1 ≤ p → 2 ≤ T → 2 * R ≤ T → Real.pi / 2 ≤ T →
      ENNReal.ofReal c * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      ENNReal.ofReal (2 * 3 ^ (((n : ℝ) + 2 * δ + 1) / 2) *
        T ^ (((n : ℝ) + 2 * δ + 1) / 2 - (n : ℝ) / p)) *
        eLpNorm (sphericalKernelConvolution (OAI.Analysis.Fourier.Radial.bochnerRieszKernel δ) f) (ENNReal.ofReal p) volume +
      ENNReal.ofReal (D * (1 + R ^ 2) / T * ∫ y, ‖f y‖) *
        OAI.Analysis.Fourier.Restriction.sphereMeasure n univ ^ (1 / p) := by
  obtain ⟨A, B, C, hC, hAB, hAs⟩ := OAI.Analysis.Fourier.Radial.bochnerRieszKernel_asymptotic hn hδ
  obtain ⟨M, hM⟩ := OAI.Analysis.Fourier.BochnerRiesz.bddAbove_norm_bochnerRieszKernel hn hδ
  have hKb (x : Space n) : ‖OAI.Analysis.Fourier.Radial.bochnerRieszKernel δ x‖ ≤ M := hM (mem_range_self x)
  have hβ : 0 ≤ ((n : ℝ) + 2 * δ + 1) / 2 := by positivity
  obtain ⟨D, hD, H⟩ := twoRadius_fourier_norm_bound hn
    (OAI.Analysis.Fourier.Radial.continuous_bochnerRieszKernel hδ).measurable hKb
    (((n : ℝ) + 2 * δ + 1) / 2) A B C hβ hC hAs
  refine ⟨‖(A : ℂ) - Complex.I * (B : ℂ)‖, D,
    norm_pos_iff.mpr (outgoing_coefficient_ne_zero hAB), hD, ?_⟩
  intro R hR f hfm hfi hfs p T hp hT hRT hpi
  exact annular_inequality_normalize hn (by linarith) (by linarith)
    (((n : ℝ) + 2 * δ + 1) / 2) _ _ _ _ _ (H R hR f hfm hfi hfs p T hp hT hRT hpi)

end OAI.Analysis.Fourier.Restriction
