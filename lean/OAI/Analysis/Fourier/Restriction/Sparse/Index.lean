import OAI.Analysis.Fourier.Restriction.Sparse.KernelMass
import OAI.Analysis.Fourier.Restriction.GramMass
import OAI.Analysis.Fourier.Restriction.Sparse.Decay

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def indexedLocalizedKernel {n N : ℕ} (u : SchwartzMap (Space n) ℂ)
    (R : ℝ) (z : Fin N → Space n) (p : Space n × (Fin N × Space n)) : ℂ :=
  localizedFourierKernel u R (z p.2.1) p.1 p.2.2

theorem measurable_indexedLocalizedKernel {n N : ℕ} (u : SchwartzMap (Space n) ℂ)
    {R : ℝ} (hR : 0 < R) (z : Fin N → Space n) :
    Measurable (indexedLocalizedKernel u R z) := by
  have hz : Measurable z := measurable_of_finite z
  have hF := (continuous_angularFourier u.integrable).measurable
  unfold indexedLocalizedKernel
  simp_rw [localizedFourierKernel_eq u hR]
  fun_prop

theorem norm_indexedLocalizedKernel_le {n N : ℕ} (u : SchwartzMap (Space n) ℂ)
    (hu : ∀ ξ, ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ‖ ≤ 1) {R : ℝ} (hR : 0 < R)
    (z : Fin N → Space n) (p : Space n × (Fin N × Space n)) :
    ‖indexedLocalizedKernel u R z p‖ ≤ R ^ n := by
  rw [indexedLocalizedKernel, norm_localizedFourierKernel u hR]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (hu _) (pow_nonneg hR.le n)

theorem finite_diagonal_sum_le {N : ℕ} (i : Fin N) (f : Fin N → ℝ≥0∞)
    {A D : ℝ≥0∞} (hi : f i ≤ A) (hj : ∀ j, j ≠ i → f j ≤ D) :
    ∑ j, f j ≤ A + (N : ℝ≥0∞) * D := by
  have H (j : Fin N) : f j ≤ (if j = i then A else 0) + D := by
    by_cases h : j = i
    · subst j
      simpa only [ite_eq_left] using hi.trans (le_add_right le_rfl)
    · simpa only [ite_eq_right h, zero_add] using hj j h
  calc
    _ ≤ ∑ j, ((if j = i then A else 0) + D) := Finset.sum_le_sum (fun j _ ↦ H j)
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]

theorem localizedFourierKernel_diagonal_gram_bound {n : ℕ} (hn : 1 ≤ n)
    (u : SchwartzMap (Space n) ℂ)
    (hu : ∀ ξ, ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ‖ ≤ 1)
    (hs : ∀ ξ, 1 / 8 ≤ ‖ξ‖ → OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ z ξ : Space n,
      (∫⁻ η, ‖∫ ω, localizedFourierKernel u R z ω ξ *
        star (localizedFourierKernel u R z ω η) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n‖ₑ) ≤
      volume (ball (0 : Space n) 1) * ENNReal.ofReal (C * R) := by
  obtain ⟨C, hC, HC⟩ := localizedFourierKernel_column hn u hu hs
  refine ⟨C, hC, ?_⟩
  intro R hR z ξ
  exact lintegral_gramKernel_le_of_row_column volume (OAI.Analysis.Fourier.Restriction.sphereMeasure n)
    (continuous_localizedFourierKernel u hR z).measurable
    (localizedFourierKernel_row u hu hs hR z) (HC R hR z) ξ

end OAI.Analysis.Fourier.Restriction
