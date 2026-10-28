import OAI.Analysis.Fourier.Restriction.LatticeBound

open _root_.MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem lattice_bound_lower_output {n : ℕ} {p q : ℝ}
    (hq : 0 < q) (hqp : q ≤ p) {C : ℝ≥0∞}
    (hbound : ∀ E : Finset (Fin n → ℤ), ∀ a : (Fin n → ℤ) → ℂ,
      eLpNorm (latticePhaseSum E a) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        C * ENNReal.ofReal ((∑ k ∈ E, ‖a k‖ ^ q) ^ (1 / q)))
    (E : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ) :
    eLpNorm (latticePhaseSum E a) (ENNReal.ofReal q) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      (C * (OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ) ^ (1 / q - 1 / p)) *
        ENNReal.ofReal ((∑ k ∈ E, ‖a k‖ ^ q) ^ (1 / q)) := by
  have hp : 0 < p := hq.trans_le hqp
  have hm : AEStronglyMeasurable (latticePhaseSum E a) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
    rw [← finitePhaseSum_integerVector]
    exact (continuous_finitePhaseSum _ _).aestronglyMeasurable
  have H := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (ENNReal.ofReal_le_ofReal hqp) hm
  have H' : eLpNorm (latticePhaseSum E a) (ENNReal.ofReal q) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      eLpNorm (latticePhaseSum E a) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) *
        (OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ) ^ (1 / q - 1 / p) := by
    simpa only [ENNReal.toReal_ofReal hq.le, ENNReal.toReal_ofReal hp.le] using H
  calc
    _ ≤ _ := H'
    _ ≤ (C * ENNReal.ofReal ((∑ k ∈ E, ‖a k‖ ^ q) ^ (1 / q))) *
        (OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ) ^ (1 / q - 1 / p) := by gcongr; exact hbound E a
    _ = _ := by ring

end OAI.Analysis.Fourier.Restriction
