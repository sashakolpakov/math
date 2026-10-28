import OAI.Analysis.Fourier.Restriction.WeightedKernel

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem polynomial_decay_sub_le {n : ℕ} (x y : Space n) {a : ℝ} (ha : 0 ≤ a) :
    (1 + ‖x - y‖) ^ (-a) ≤ (1 + ‖x‖) ^ (-a) * (1 + ‖y‖) ^ a := by
  have hx : 0 < 1 + ‖x‖ := by positivity
  have hy : 0 < 1 + ‖y‖ := by positivity
  have hxy : 0 < 1 + ‖x - y‖ := by positivity
  have ht : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - y) y
  have hbase : 1 + ‖x‖ ≤ (1 + ‖x - y‖) * (1 + ‖y‖) := by
    nlinarith [mul_nonneg (norm_nonneg (x - y)) (norm_nonneg y)]
  have H := Real.rpow_le_rpow hx.le hbase ha
  rw [Real.mul_rpow hxy.le hy.le] at H
  rw [Real.rpow_neg hx.le, Real.rpow_neg hxy.le]
  have hxa : 0 < (1 + ‖x‖) ^ a := Real.rpow_pos_of_pos hx a
  have hxya : 0 < (1 + ‖x - y‖) ^ a := Real.rpow_pos_of_pos hxy a
  rw [inv_mul_eq_div, inv_eq_one_div, div_le_div_iff₀ hxya hxa]
  simpa only [one_mul, mul_comm] using H

theorem sphericalExtension_fourier_mul_decay {n : ℕ} {f g : Space n → ℂ} {a C : ℝ}
    (hf : Integrable f) (hg : Integrable g (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hfw : Integrable (fun y ↦ ‖f y‖ * (1 + ‖y‖) ^ a))
    (hdecay : ∀ x, ‖OAI.Analysis.Fourier.Restriction.sphericalExtension g x‖ ≤ C * (1 + ‖x‖) ^ (-a)) (x : Space n) :
    ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ω * g ω) x‖ ≤
      (C * ∫ y, ‖f y‖ * (1 + ‖y‖) ^ a) * (1 + ‖x‖) ^ (-a) := by
  rw [sphericalExtension_fourier_mul hf hg]
  have hi : Integrable (fun y ↦ f y * OAI.Analysis.Fourier.Restriction.sphericalExtension g (x - y)) := by
    have H := hf.bdd_mul
      (((continuous_sphericalExtension hg).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun y ↦ norm_sphericalExtension_le g (x - y))
    simpa only [Function.comp_apply, Pi.sub_apply, id_eq, mul_comm] using H
  calc
    _ ≤ ∫ y, ‖f y * OAI.Analysis.Fourier.Restriction.sphericalExtension g (x - y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (C * (1 + ‖x‖) ^ (-a)) * (‖f y‖ * (1 + ‖y‖) ^ a) := by
      apply integral_mono hi.norm (hfw.const_mul _)
      intro y
      dsimp only
      rw [norm_mul]
      calc
        _ ≤ ‖f y‖ * (C * (1 + ‖x - y‖) ^ (-a)) :=
          mul_le_mul_of_nonneg_left (hdecay (x - y)) (norm_nonneg _)
        _ ≤ ‖f y‖ * (C * ((1 + ‖x‖) ^ (-a) * (1 + ‖y‖) ^ a)) := by
          gcongr
          exact polynomial_decay_sub_le x y ha
        _ = _ := by ring
    _ = _ := by rw [integral_const_mul]; ring

theorem sphericalExtension_fourier_decay {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Space n → ℂ, Integrable f →
      Integrable (fun y ↦ ‖f y‖ * (1 + ‖y‖) ^ (((n : ℝ) - 1) / 2)) →
      ∀ x, ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) x‖ ≤
        (C * ∫ y, ‖f y‖ * (1 + ‖y‖) ^ (((n : ℝ) - 1) / 2)) *
          (1 + ‖x‖) ^ (-((n : ℝ) - 1) / 2) := by
  obtain ⟨C, hC, hdecay⟩ := OAI.Analysis.Fourier.Radial.sphericalExtension_one_polynomial_decay hn
  refine ⟨C, hC, ?_⟩
  intro f hf hfw x
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have H := sphericalExtension_fourier_mul_decay hf (integrable_const (1 : ℂ))
    (show 0 ≤ ((n : ℝ) - 1) / 2 by linarith) hC.le hfw (by simpa only [neg_div] using hdecay) x
  simpa only [mul_one, neg_div] using H

theorem sphericalExtension_fourier_product_decay {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ f g : Space n → ℂ, Integrable f → Integrable g →
      Integrable (fun y ↦ ‖f y‖ * (1 + ‖y‖) ^ (((n : ℝ) - 1) / 2)) →
      Integrable (fun y ↦ ‖g y‖ * (1 + ‖y‖) ^ (((n : ℝ) - 1) / 2)) →
      ∀ x, ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ω * OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ω) x‖ ≤
        (C * (∫ y, ‖f y‖ * (1 + ‖y‖) ^ (((n : ℝ) - 1) / 2)) *
          (∫ y, ‖g y‖ * (1 + ‖y‖) ^ (((n : ℝ) - 1) / 2))) *
            (1 + ‖x‖) ^ (-((n : ℝ) - 1) / 2) := by
  obtain ⟨C, hC, HC⟩ := sphericalExtension_fourier_decay hn
  refine ⟨C, hC, ?_⟩
  intro f g hf hg hfw hgw x
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 ≤ C * ∫ y, ‖g y‖ * (1 + ‖y‖) ^ (((n : ℝ) - 1) / 2) := by
    positivity
  have H := sphericalExtension_fourier_mul_decay hf (integrable_angularFourier_sphere hg)
    (show 0 ≤ ((n : ℝ) - 1) / 2 by linarith) hpos hfw
    (by simpa only [neg_div] using HC g hg hgw) x
  convert H using 1 ; ring_nf

end OAI.Analysis.Fourier.Restriction
