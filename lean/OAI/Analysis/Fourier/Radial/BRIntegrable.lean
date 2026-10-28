import OAI.Analysis.Fourier.Radial.BRDecay
import OAI.Analysis.Fourier.BochnerRiesz.Multiplier

open OAI.Analysis.Fourier.Wave

/-! Sharp integrability threshold for the Bochner--Riesz convolution kernel. -/

open _root_.MeasureTheory
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem integrable_complex_bochnerRieszSymbol_unit {n : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun ξ : Space n => (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 ξ : ℂ)) := by
  exact Complex.ofRealCLM.integrable_comp (integrable_bochnerRieszSymbol_unit hδ)

theorem continuous_bochnerRieszKernel {n : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    Continuous (bochnerRieszKernel (n := n) δ) := by
  exact OAI.Analysis.Fourier.BochnerRiesz.continuous_angularInverse (integrable_complex_bochnerRieszSymbol_unit hδ)

theorem integrable_bochnerRieszKernel {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ : ((n : ℝ) - 1) / 2 < δ) : Integrable (bochnerRieszKernel (n := n) δ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < δ := by linarith
  obtain ⟨C, _, hC⟩ := bochnerRieszKernel_polynomial_decay hn hd
  have hi : Integrable (fun x : Space n => (1 + ‖x‖) ^ (-((n : ℝ) + 2 * δ + 1) / 2)) := by
    have H : Integrable (fun x : Space n => (1 + ‖x‖) ^ (-(((n : ℝ) + 2 * δ + 1) / 2))) := by
      apply integrable_one_add_norm
      simp only [Space, finrank_euclideanSpace, Fintype.card_fin]
      linarith
    convert H using 1
    funext x
    congr 1
    ring
  apply (hi.const_mul C).mono' (continuous_bochnerRieszKernel hd).aestronglyMeasurable
  exact Filter.Eventually.of_forall hC

end OAI.Analysis.Fourier.Radial
