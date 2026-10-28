import OAI.Analysis.Fourier.Restriction.WeakInterpolation
import OAI.Analysis.Fourier.Restriction.Interpolation

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem measure_norm_gt_le_moment {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) {g : Y → ℂ} (hg : Measurable g)
    {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    ν {y | t < ‖g y‖} ≤ (∫⁻ y, ‖g y‖ₑ ^ p ∂ν) / ENNReal.ofReal t ^ p := by
  have hsubset : {y | t < ‖g y‖} ⊆ {y | ENNReal.ofReal t ^ p ≤ ‖g y‖ₑ ^ p} := by
    intro y hy
    apply ENNReal.rpow_le_rpow _ hp.le
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hy.le
  exact (measure_mono hsubset).trans (meas_ge_le_lintegral_div
    (hg.enorm.pow_const p).aemeasurable (by positivity)
    (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top))

end OAI.Analysis.Fourier.Restriction
