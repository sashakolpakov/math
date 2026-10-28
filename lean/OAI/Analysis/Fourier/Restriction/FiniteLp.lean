import OAI.Analysis.Fourier.Restriction.Sparse.Operator

open _root_.MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem eLpNorm_finite_prod {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    {N : ℕ} {f : Fin N × X → ℂ} (hf : Measurable f) {p : ℝ} (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) (Measure.count.prod μ) =
      (∑ i : Fin N, eLpNorm (fun x ↦ f (i, x)) (ENNReal.ofReal p) μ ^ p) ^ (1 / p) := by
  have hi (i : Fin N) : eLpNorm (fun x ↦ f (i, x)) (ENNReal.ofReal p) μ ^ p =
      ∫⁻ x, ‖f (i, x)‖ₑ ^ p ∂μ := by
    have hfi : Measurable (fun x ↦ f (i, x)) := hf.comp (measurable_const.prodMk measurable_id)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
      hfi.aestronglyMeasurable,
      ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul,
      one_div_mul_cancel hp.ne', ENNReal.rpow_one]
  simp_rw [hi]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
    hf.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le,
    lintegral_prod _ (by fun_prop), lintegral_count, tsum_fintype]

theorem eLpNorm_finite_family_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {N : ℕ} {f : Fin N × X → ℂ}
    (hf : Measurable f) {p : ℝ} (hp : 0 < p) (b : Fin N → ℝ≥0∞) (D : ℝ≥0∞)
    (h : ∀ i, eLpNorm (fun x ↦ f (i, x)) (ENNReal.ofReal p) μ ≤ D * b i) :
    eLpNorm f (ENNReal.ofReal p) (Measure.count.prod μ) ≤
      D * (∑ i, b i ^ p) ^ (1 / p) := by
  rw [eLpNorm_finite_prod μ hf hp]
  calc
    _ ≤ (∑ i, (D * b i) ^ p) ^ (1 / p) := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      exact Finset.sum_le_sum (fun i _ ↦ ENNReal.rpow_le_rpow (h i) hp.le)
    _ = (D ^ p * ∑ i, b i ^ p) ^ (1 / p) := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
      rw [Finset.mul_sum]
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
        mul_one_div_cancel hp.ne', ENNReal.rpow_one]

end OAI.Analysis.Fourier.Restriction
