import OAI.Analysis.Fourier.SquareFunction.Maximal.BR
import OAI.Analysis.Fourier.Radial.BRConjecture

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction


theorem tendsto_bochnerRieszSymbol_radius {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (ξ : Space n) :
    Tendsto (fun R : ℝ => OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ R ξ) atTop (𝓝 1) := by
  have hq : Tendsto (fun R : ℝ => ‖ξ‖ / R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0))
  have ht : Tendsto (fun R : ℝ => max (1 - (‖ξ‖ / R) ^ 2) 0) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub (hq.pow 2)).max
      (tendsto_const_nhds (x := (0 : ℝ)))
  simpa only [Real.one_rpow, Function.comp_def, OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol] using
    (Real.continuous_rpow_const hδ).continuousAt.tendsto.comp ht

/-- Pointwise summability on Schwartz functions, directly from Fourier
inversion and dominated convergence; this does not assume local smoothing. -/
theorem tendsto_bochnerRiesz_schwartz {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Tendsto (fun R : ℝ => OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x) atTop (𝓝 (f x)) := by
  have he : f x = 𝓕⁻ (fun ξ => (𝓕 f : SchwartzMap (Space n) ℂ) ξ) x := by
    rw [← SchwartzMap.fourierInv_coe, fourierInv_fourier_eq]
  rw [he]
  simp only [OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz_eq_fourierInv, SchwartzMap.fourier_coe,
    fourierInv_eq_spatialPhase_smul]
  apply tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖(𝓕 f : SchwartzMap (Space n) ℂ) ξ‖)
  · exact Eventually.of_forall (fun R => (continuous_spatialPhase x).aestronglyMeasurable.smul
      ((OAI.Analysis.Fourier.BochnerRiesz.measurable_bochnerRieszCyclesSymbol hδ R).mul (𝓕 f).integrable.aestronglyMeasurable))
  · exact Eventually.of_forall (fun R => Eventually.of_forall (fun ξ => by
      simpa only [norm_smul, norm_spatialPhase, one_mul, norm_mul, SchwartzMap.fourier_coe] using
        mul_le_mul_of_nonneg_right (OAI.Analysis.Fourier.BochnerRiesz.norm_bochnerRieszCyclesSymbol_le hδ R ξ) (norm_nonneg _)))
  · exact (𝓕 f).integrable.norm
  · apply Eventually.of_forall
    intro ξ
    have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_bochnerRieszSymbol_radius hδ ((2 * Real.pi) • ξ))
    have H := (tendsto_const_nhds (x := spatialPhase x ξ)).smul
      (ht.mul (tendsto_const_nhds (x := (𝓕 f : SchwartzMap (Space n) ℂ) ξ)))
    simpa only [OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszCyclesSymbol, Complex.ofReal_one, one_mul,
      Function.comp_def, SchwartzMap.fourier_coe] using H

end OAI.Analysis.Fourier.SquareFunction
