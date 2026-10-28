import Mathlib

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- The positive-kernel quadratic form of Schur's test. Both integrals
are allowed to be infinite, so the lemma does not presuppose the bound
that it proves. -/
theorem schur_quadratic_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    {k : X × X → ℝ≥0∞} (hk : Measurable k)
    {a : X → ℝ} (ha : Measurable a) (han : ∀ x, 0 ≤ a x)
    {A : ℝ≥0∞} (hrow : ∀ x, (∫⁻ z, k (x, z) ∂μ) ≤ A)
    (hcol : ∀ z, (∫⁻ x, k (x, z) ∂μ) ≤ A) :
    (∫⁻ w, ENNReal.ofReal (a w.1) * ENNReal.ofReal (a w.2) * k w ∂μ.prod μ) ≤
      A * ∫⁻ x, ENNReal.ofReal (a x) ^ (2 : ℝ) ∂μ := by
  have hsq (x : X) : ENNReal.ofReal (a x) ^ (2 : ℝ) = ENNReal.ofReal ((a x) ^ 2) := by
    simp only [ENNReal.rpow_two, pow_two, ENNReal.ofReal_mul (han x)]
  have hm1 : Measurable (fun w : X × X ↦ ENNReal.ofReal (a w.1) ^ (2 : ℝ) * k w) := by
    fun_prop
  have hm2 : Measurable (fun w : X × X ↦ ENNReal.ofReal (a w.2) ^ (2 : ℝ) * k w) := by
    fun_prop
  have H1 : (∫⁻ w, ENNReal.ofReal (a w.1) ^ (2 : ℝ) * k w ∂μ.prod μ) ≤
      A * ∫⁻ x, ENNReal.ofReal (a x) ^ (2 : ℝ) ∂μ := by
    rw [lintegral_prod _ hm1.aemeasurable,
      ← lintegral_const_mul _ (ha.ennreal_ofReal.pow_const 2)]
    apply lintegral_mono
    intro x
    change (∫⁻ z, ENNReal.ofReal (a x) ^ (2 : ℝ) * k (x, z) ∂μ) ≤ _
    have hkr : Measurable (fun z ↦ k (x, z)) := by fun_prop
    rw [lintegral_const_mul _ hkr]
    calc
      _ ≤ ENNReal.ofReal (a x) ^ (2 : ℝ) * A := mul_le_mul le_rfl (hrow x) zero_le zero_le
      _ = _ := mul_comm _ _
  have H2 : (∫⁻ w, ENNReal.ofReal (a w.2) ^ (2 : ℝ) * k w ∂μ.prod μ) ≤
      A * ∫⁻ x, ENNReal.ofReal (a x) ^ (2 : ℝ) ∂μ := by
    rw [lintegral_prod_symm _ hm2.aemeasurable,
      ← lintegral_const_mul _ (ha.ennreal_ofReal.pow_const 2)]
    apply lintegral_mono
    intro z
    change (∫⁻ x, ENNReal.ofReal (a z) ^ (2 : ℝ) * k (x, z) ∂μ) ≤ _
    have hkc : Measurable (fun x ↦ k (x, z)) := by fun_prop
    rw [lintegral_const_mul _ hkc]
    calc
      _ ≤ ENNReal.ofReal (a z) ^ (2 : ℝ) * A := mul_le_mul le_rfl (hcol z) zero_le zero_le
      _ = _ := mul_comm _ _
  calc
    _ ≤ ∫⁻ w, ENNReal.ofReal (1 / 2 : ℝ) *
        (ENNReal.ofReal (a w.1) ^ (2 : ℝ) * k w + ENNReal.ofReal (a w.2) ^ (2 : ℝ) * k w) ∂μ.prod μ := by
      apply lintegral_mono
      intro w
      have H : ENNReal.ofReal (a w.1) * ENNReal.ofReal (a w.2) ≤
          ENNReal.ofReal (1 / 2 : ℝ) *
            (ENNReal.ofReal (a w.1) ^ (2 : ℝ) + ENNReal.ofReal (a w.2) ^ (2 : ℝ)) := by
        rw [hsq, hsq, ← ENNReal.ofReal_mul (han _),
          ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        nlinarith [sq_nonneg (a w.1 - a w.2)]
      calc
        _ ≤ (ENNReal.ofReal (1 / 2 : ℝ) *
            (ENNReal.ofReal (a w.1) ^ (2 : ℝ) + ENNReal.ofReal (a w.2) ^ (2 : ℝ))) * k w :=
          mul_le_mul H le_rfl zero_le zero_le
        _ = _ := by ring
    _ = ENNReal.ofReal (1 / 2 : ℝ) *
        ((∫⁻ w, ENNReal.ofReal (a w.1) ^ (2 : ℝ) * k w ∂μ.prod μ) +
          ∫⁻ w, ENNReal.ofReal (a w.2) ^ (2 : ℝ) * k w ∂μ.prod μ) := by
      have hm12 : Measurable (fun w : X × X ↦
          ENNReal.ofReal (a w.1) ^ (2 : ℝ) * k w + ENNReal.ofReal (a w.2) ^ (2 : ℝ) * k w) := by
        fun_prop
      rw [lintegral_const_mul _ hm12, lintegral_add_left hm1]
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) *
        (A * (∫⁻ x, ENNReal.ofReal (a x) ^ (2 : ℝ) ∂μ) +
          A * ∫⁻ x, ENNReal.ofReal (a x) ^ (2 : ℝ) ∂μ) := by gcongr
    _ = _ := by
      rw [mul_add, ← add_mul]
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num

theorem schur_complex_quadratic_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    {K : X × X → ℂ} (hK : Measurable K)
    {f : X → ℂ} (hf : Measurable f)
    {A : ℝ≥0∞} (hrow : ∀ x, (∫⁻ z, ‖K (x, z)‖ₑ ∂μ) ≤ A)
    (hcol : ∀ z, (∫⁻ x, ‖K (x, z)‖ₑ ∂μ) ≤ A) :
    ‖∫ w, f w.1 * star (f w.2) * K w ∂μ.prod μ‖ₑ ≤
      A * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  have H := schur_quadratic_bound μ hK.enorm hf.norm (fun x ↦ norm_nonneg _) hrow hcol
  simp only [ofReal_norm] at H
  calc
    _ ≤ ∫⁻ w, ‖f w.1 * star (f w.2) * K w‖ₑ ∂μ.prod μ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ w, ‖f w.1‖ₑ * ‖f w.2‖ₑ * ‖K w‖ₑ ∂μ.prod μ := by
      apply lintegral_congr
      intro w
      simp
    _ ≤ _ := H

end OAI.Analysis.Fourier.Restriction
