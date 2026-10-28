import OAI.Analysis.Fourier.Restriction.ThinNorm

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem inverse_ofReal_positive {a : ℝ} (ha : 0 < a) :
    (ENNReal.ofReal a)⁻¹ = ENNReal.ofReal a⁻¹ := by
  have H := ENNReal.ofReal_rpow_of_pos ha (p := -1)
  simpa only [ENNReal.rpow_neg_one, Real.rpow_neg_one] using H

theorem thin_annulus_scale {n : ℕ} (hn : 1 ≤ n) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    (ENNReal.ofReal (c * δ ^ (n - 1)))⁻¹ * volume (ball (0 : Space n) (2 * δ)) =
      (ENNReal.ofReal (2 ^ n / c) * volume (ball (0 : Space n) 1)) * ENNReal.ofReal δ := by
  rw [inverse_ofReal_positive (by positivity),
    Measure.addHaar_ball_of_pos volume _ (by positivity : 0 < 2 * δ)]
  simp only [Space, finrank_euclideanSpace_fin]
  have hp : δ ^ n = δ ^ (n - 1) * δ := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have he : (c * δ ^ (n - 1))⁻¹ * (2 * δ) ^ n = (2 ^ n / c) * δ := by
    rw [mul_pow, hp]
    field_simp

  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), he, ENNReal.ofReal_mul (by positivity)]
  ring

theorem thin_annulus_norm_of_translated_sphere_bound {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 0 < p) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ F : Space n → ℂ,
      Measurable F → ∀ B : ℝ≥0∞,
      (∀ v : Space n, eLpNorm (fun ω ↦ F (ω + v)) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤ B) →
      eLpNorm F (ENNReal.ofReal p) (volume.restrict (sphericalAnnulus δ)) ≤
        A * ENNReal.ofReal δ ^ (1 / p) * B := by
  obtain ⟨c, hc, HC⟩ := sphere_thickening_norm hn
  let A := (ENNReal.ofReal (2 ^ n / c) * volume (ball (0 : Space n) 1)) ^ (1 / p)
  have hA : A ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ball_lt_top : volume (ball (0 : Space n) 1) < ⊤).ne)
  refine ⟨A, hA, ?_⟩
  intro δ hδ hδhalf F hF B hB
  have H := HC δ hδ hδhalf F hF p hp B hB
  rwa [thin_annulus_scale hn hc hδ, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)] at H

end OAI.Analysis.Fourier.Restriction
