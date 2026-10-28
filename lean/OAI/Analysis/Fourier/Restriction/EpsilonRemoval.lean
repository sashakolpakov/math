import OAI.Analysis.Fourier.Restriction.DiscreteEpsilon
import OAI.Analysis.Fourier.Restriction.LatticeExponent
import OAI.Analysis.Fourier.Restriction.LatticeLimit

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- Full Euclidean epsilon removal from the sparse-ball estimate.
The conclusion is an actual Fourier restriction estimate for every
integrable input, without support restrictions or residual losses. -/
theorem sparse_bound_implies_restriction {n : ℕ} {p q : ℝ}
    (hq : 1 ≤ q) (hqp : q < p) {D : ℕ} (hD : 0 < D)
    (hSparse : ∀ α > (0 : ℝ), ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      SparseFourierBound n (ENNReal.ofReal p) α D C) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : Space n → ℂ, Integrable f →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal q) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        C * eLpNorm f (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := by linarith
  obtain ⟨C, hCt, hC⟩ := sparse_bound_implies_lattice_bound hq hqp hD hSparse
  have hexp : 0 ≤ 1 / q - 1 / p :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hq0 hqp.le)
  refine ⟨C * (OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ) ^ (1 / q - 1 / p), ?_, ?_⟩
  · exact ENNReal.mul_ne_top hCt
      (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top _ _))
  · intro f hf
    exact restriction_of_lattice_bound hq
      (lattice_bound_lower_output hq0 hqp.le hC) hf

end OAI.Analysis.Fourier.Restriction
