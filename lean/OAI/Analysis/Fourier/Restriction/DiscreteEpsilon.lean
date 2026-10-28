import OAI.Analysis.Fourier.Restriction.BoundedPhases
import OAI.Analysis.Fourier.Restriction.PhaseStrong
import OAI.Analysis.Fourier.Restriction.LatticeBound

open _root_.MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- Quantitative epsilon removal on the integer lattice. This conclusion
has no support-size loss and one constant for all finite coefficient sets. -/
theorem sparse_bound_implies_lattice_bound {n : ℕ} {p q : ℝ}
    (hq : 1 ≤ q) (hqp : q < p) {D : ℕ} (hD : 0 < D)
    (hSparse : ∀ α > (0 : ℝ), ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      SparseFourierBound n (ENNReal.ofReal p) α D C) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ E : Finset (Fin n → ℤ), ∀ a : (Fin n → ℤ) → ℂ,
      eLpNorm (latticePhaseSum E a) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        C * ENNReal.ofReal ((∑ k ∈ E, ‖a k‖ ^ q) ^ (1 / q)) := by
  have hq0 : 0 < q := by linarith
  have hp : 1 ≤ p := hq.trans hqp.le
  have hp0 : 0 < p := hq0.trans hqp
  have hgap : 0 < 1 / q - 1 / p := sub_pos.mpr (one_div_lt_one_div_of_lt hq0 hqp)
  let ε : ℝ := (1 / q - 1 / p) / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hs : 0 ≤ ε + 1 / p := by positivity
  have hqs : q * (ε + 1 / p) < 1 := by
    have H : ε + 1 / p < 1 / q := by dsimp [ε]; linarith
    have H' := mul_lt_mul_of_pos_left H hq0
    simpa only [mul_one_div_cancel hq0.ne'] using H'
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  obtain ⟨A, hAt, hA⟩ := unit_ball_small_loss_of_sparse hpE hD hSparse hε
  obtain ⟨B, hBt, hB⟩ := bounded_phases_of_unit_ball_loss hp0 hε hAt hA
  refine ⟨phaseInterpolationConstant q (ε + 1 / p) B,
    phaseInterpolationConstant_ne_top hBt, ?_⟩
  apply latticePhaseSum_bound_of_separated
  intro E hsep a
  apply finitePhaseSum_strong_bound E hp hq0 hs hqs _ a
  intro S hSE b hb
  exact hB S (fun z hz w hw hzw ↦ hsep z (hSE hz) w (hSE hw) hzw) b hb

end OAI.Analysis.Fourier.Restriction
