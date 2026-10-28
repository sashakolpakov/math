import OAI.Analysis.Fourier.Restriction.Sparse.Operator
import OAI.Analysis.Fourier.Restriction.Sparse.Annulus
import OAI.Analysis.Fourier.Restriction.FiniteLp

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem measurable_finite_fourier {n N : ℕ} (g : Fin N → Space n → ℂ)
    (hg : ∀ i, Integrable (g i)) :
    Measurable (fun p : Fin N × Space n ↦ OAI.Analysis.Fourier.LocalSmoothing.angularFourier (g p.1) p.2) := by
  exact measurable_from_prod_countable_right (fun i ↦ (continuous_angularFourier (hg i)).measurable)

theorem integrable_finite_fourier {n N : ℕ} (g : Fin N → Space n → ℂ)
    (hg : ∀ i, Integrable (g i)) (ν : Measure (Space n)) [IsFiniteMeasure ν] :
    Integrable (fun p : Fin N × Space n ↦ OAI.Analysis.Fourier.LocalSmoothing.angularFourier (g p.1) p.2) (Measure.count.prod ν) := by
  let M : ℝ := ∑ i, ∫ x, ‖g i x‖
  apply (integrable_const M).mono' (measurable_finite_fourier g hg).aestronglyMeasurable
  filter_upwards [] with p
  exact (norm_angularFourier_le_integral_norm (g p.1) p.2).trans
    (Finset.single_le_sum (f := fun i : Fin N ↦ ∫ x, ‖g i x‖)
      (fun i _ ↦ integral_nonneg (fun x ↦ norm_nonneg (g i x))) (Finset.mem_univ p.1))

theorem integralKernel_finite_sum {n N : ℕ} (u : SchwartzMap (Space n) ℂ)
    (hu : ∀ ξ, ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ‖ ≤ 1) {R : ℝ} (hR : 0 < R)
    (z : Fin N → Space n) (ν : Measure (Space n)) [IsFiniteMeasure ν]
    {f : Fin N × Space n → ℂ} (hf : Integrable f (Measure.count.prod ν)) (ω : Space n) :
    integralKernel (Measure.count.prod ν) (indexedLocalizedKernel u R z) f ω =
      ∑ i, ∫ ξ, localizedFourierKernel u R (z i) ω ξ * f (i, ξ) ∂ν := by
  have hi := integrable_kernel_mul (Measure.count.prod ν)
    (measurable_indexedLocalizedKernel u hR z) (norm_indexedLocalizedKernel_le u hu hR z) hf ω
  rw [integralKernel, integral_prod _ hi]
  simp only [integral_count, indexedLocalizedKernel]

end OAI.Analysis.Fourier.Restriction
