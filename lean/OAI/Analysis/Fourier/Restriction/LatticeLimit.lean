import OAI.Analysis.Fourier.Restriction.LatticeAverage
import OAI.Analysis.Fourier.Restriction.LatticeBoxes

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology RealInnerProductSpace
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem latticeAverage_eq_sum_cell_integrals {n : ℕ} (E : Finset (Fin n → ℤ))
    {f : Space n → ℂ} (hf : Integrable f) (ξ : Space n) :
    latticeAverage E f ξ = ∑ k ∈ E, ∫ y in OAI.Analysis.Fourier.WavePackets.unitCell n,
      Complex.exp (-Complex.I * ((inner ℝ (OAI.Analysis.Fourier.WavePackets.integerVector k + y) ξ : ℝ) : ℂ)) *
        f (OAI.Analysis.Fourier.WavePackets.integerVector k + y) := by
  unfold latticeAverage latticePhaseSum
  simp_rw [Finset.mul_sum]
  have he (k : Fin n → ℤ) (y : Space n) :
      Complex.exp (-Complex.I * ((inner ℝ y ξ : ℝ) : ℂ)) *
        (f (OAI.Analysis.Fourier.WavePackets.integerVector k + y) *
          Complex.exp (-Complex.I * ((inner ℝ (OAI.Analysis.Fourier.WavePackets.integerVector k) ξ : ℝ) : ℂ))) =
      Complex.exp (-Complex.I * ((inner ℝ (OAI.Analysis.Fourier.WavePackets.integerVector k + y) ξ : ℝ) : ℂ)) *
        f (OAI.Analysis.Fourier.WavePackets.integerVector k + y) := by
    simp only [inner_add_left, Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  simp_rw [he]
  apply integral_finsetSum
  intro k hk
  exact ((measurePreserving_add_left volume (OAI.Analysis.Fourier.WavePackets.integerVector k)).integrable_comp_of_integrable
    (angularFourier_integrand_integrable hf ξ)).integrableOn

theorem tendsto_latticeAverage {n : ℕ} {f : Space n → ℂ}
    (hf : Integrable f) (ξ : Space n) :
    Tendsto (fun N ↦ latticeAverage (latticeBox n N) f ξ)
      atTop (𝓝 (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ)) := by
  have H := tendsto_unitCell_integral_boxes (angularFourier_integrand_integrable hf ξ)
  simpa only [← latticeAverage_eq_sum_cell_integrals _ hf ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier] using H

/-- A uniform lattice restriction bound gives the genuine Euclidean
restriction bound, by probability-cell averaging and an absolutely
convergent tiling limit. -/
theorem restriction_of_lattice_bound_measurable {n : ℕ} {q : ℝ}
    (hq : 1 ≤ q) {C : ℝ≥0∞}
    (hbound : ∀ E : Finset (Fin n → ℤ), ∀ a : (Fin n → ℤ) → ℂ,
      eLpNorm (latticePhaseSum E a) (ENNReal.ofReal q) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        C * ENNReal.ofReal ((∑ k ∈ E, ‖a k‖ ^ q) ^ (1 / q)))
    {f : Space n → ℂ} (hfm : Measurable f) (hfi : Integrable f) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal q) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      C * eLpNorm f (ENNReal.ofReal q) volume := by
  apply OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_le_of_tendsto_pointwise (OAI.Analysis.Fourier.Restriction.sphereMeasure n)
    (fun N ↦ (measurable_latticeAverage (latticeBox n N) hfm).aestronglyMeasurable)
    (continuous_angularFourier hfi).aestronglyMeasurable
    (tendsto_latticeAverage hfi) (by linarith)
  intro N
  exact eLpNorm_latticeAverage_le hq hbound _ hfm

theorem restriction_of_lattice_bound {n : ℕ} {q : ℝ}
    (hq : 1 ≤ q) {C : ℝ≥0∞}
    (hbound : ∀ E : Finset (Fin n → ℤ), ∀ a : (Fin n → ℤ) → ℂ,
      eLpNorm (latticePhaseSum E a) (ENNReal.ofReal q) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        C * ENNReal.ofReal ((∑ k ∈ E, ‖a k‖ ^ q) ^ (1 / q)))
    {f : Space n → ℂ} (hfi : Integrable f) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal q) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      C * eLpNorm f (ENNReal.ofReal q) volume := by
  let g := hfi.aestronglyMeasurable.mk f
  have heq : f =ᵐ[volume] g := hfi.aestronglyMeasurable.ae_eq_mk
  have H := restriction_of_lattice_bound_measurable hq hbound
    hfi.aestronglyMeasurable.measurable_mk (hfi.congr heq)
  have hF : OAI.Analysis.Fourier.LocalSmoothing.angularFourier f = OAI.Analysis.Fourier.LocalSmoothing.angularFourier g := funext (angularFourier_congr_ae heq)
  rwa [← hF, ← eLpNorm_congr_ae heq] at H

end OAI.Analysis.Fourier.Restriction
