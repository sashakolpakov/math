import OAI.Analysis.Fourier.BochnerRiesz.DualityPartner

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem enorm_integral_mul_le_eLpNorm {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℂ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) {p q : ℝ} (hpq : p.HolderConjugate q) :
    ‖∫ x, f x * g x ∂μ‖ₑ ≤ eLpNorm f (ENNReal.ofReal p) μ * eLpNorm g (ENNReal.ofReal q) μ := by
  have := hpq.ennrealOfReal
  calc
    _ ≤ ∫⁻ x, ‖f x * g x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun x ↦ f x * g x) 1 μ := (eLpNorm_one_eq_lintegral_enorm (hf.mul hg)).symm
    _ ≤ _ := by
      simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_def] using
        (eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal p) (q := ENNReal.ofReal q) (r := 1) hf hg)

theorem enorm_integral_complexDualityPartner {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {p : ℝ} (hp : 1 < p) {f : X → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    ‖∫ x, complexDualityPartner p (f x) * f x ∂μ‖ₑ = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  have hp0 : 0 < p := by linarith
  have hi : Integrable (fun x ↦ ‖f x‖ ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      hf.integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top
  simp_rw [complexDualityPartner_mul hp]
  rw [integral_complex_ofReal, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)),
    ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun x ↦ by positivity))]
  rw [eLpNorm_rpow_eq_lintegral hp0 hf.aestronglyMeasurable]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ofReal_norm]

theorem eLpNorm_le_of_integral_mul_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {p : ℝ} (hp : 1 < p) {f : X → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) μ) {A : ℝ≥0∞}
    (hbound : ∀ g : X → ℂ, MemLp g (ENNReal.ofReal (p / (p - 1))) μ →
      ‖∫ x, g x * f x ∂μ‖ₑ ≤ A * eLpNorm g (ENNReal.ofReal (p / (p - 1))) μ) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ A := by
  by_cases hAt : A = ⊤
  · simp [hAt]
  let N := eLpNorm f (ENNReal.ofReal p) μ
  have hNt : N ≠ ⊤ := hf.ne
  by_cases hN0 : N = 0
  · change N ≤ A
    simp [hN0]
  have hNpos : 0 < N.toReal := ENNReal.toReal_pos hN0 hNt
  have hpartner : MemLp (fun x ↦ complexDualityPartner p (f x))
      (ENNReal.ofReal (p / (p - 1))) μ := by
    change eLpNorm _ _ _ < ⊤
    rw [eLpNorm_complexDualityPartner μ hf.aestronglyMeasurable hp]
    exact (ENNReal.rpow_ne_top_of_nonneg (by linarith) hf.ne).lt_top
  have H := hbound (fun x ↦ complexDualityPartner p (f x)) hpartner
  rw [enorm_integral_complexDualityPartner μ hp hf,
    eLpNorm_complexDualityPartner μ hf.aestronglyMeasurable hp] at H
  change N ^ p ≤ A * N ^ (p - 1) at H
  have Hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hAt (ENNReal.rpow_ne_top_of_nonneg (by linarith) hNt)) H
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at Hr
  have he : N.toReal ^ p = N.toReal * N.toReal ^ (p - 1) := by
    conv_lhs => rw [show p = 1 + (p - 1) by ring, Real.rpow_add hNpos, Real.rpow_one]
  rw [he] at Hr
  have Hfinal : N.toReal ≤ A.toReal := by
    by_contra h
    have Hpos := mul_pos (sub_pos.mpr (lt_of_not_ge h)) (Real.rpow_pos_of_pos hNpos (p - 1))
    nlinarith
  exact (ENNReal.toReal_le_toReal hNt hAt).mp Hfinal

end OAI.Analysis.Fourier.BochnerRiesz
