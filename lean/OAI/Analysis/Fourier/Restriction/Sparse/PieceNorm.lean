import OAI.Analysis.Fourier.Restriction.Sparse.Pieces

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem integrable_sparsePiece {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R) (hu : ∀ x, ‖x‖ ≤ 1 → c ≤ ‖u x‖)
    (z : Space n) {f : Space n → ℂ} (hfm : Measurable f) (hf : Integrable f) :
    Integrable (sparsePiece u R z f) := by
  have ht : Integrable (fun x ↦ f (x + z)) :=
    (measurePreserving_add_right volume z).integrable_comp_of_integrable hf
  have hi : Integrable ((ball (0 : Space n) R).indicator (fun x ↦ f (x + z))) :=
    ht.indicator measurableSet_ball
  apply (hi.norm.const_mul c⁻¹).mono' (measurable_sparsePiece u R z hfm).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_sparsePiece_le u hc hR hu z f)

theorem sparsePiece_indicator_translate {n : ℕ} (R : ℝ) (z : Space n)
    (f : Space n → ℂ) (x : Space n) :
    (ball (0 : Space n) R).indicator (fun y ↦ f (y + z)) x =
      (ball z R).indicator f (x + z) := by
  have he : x ∈ ball (0 : Space n) R ↔ x + z ∈ ball z R := by
    simp only [mem_ball, dist_eq_norm, sub_zero, add_sub_cancel_right]
  by_cases hx : x ∈ ball (0 : Space n) R
  · rw [indicator_of_mem hx, indicator_of_mem (he.mp hx)]
  · rw [indicator_of_notMem hx, indicator_of_notMem (fun h ↦ hx (he.mpr h))]

theorem eLpNorm_sparsePiece_le {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R) (hu : ∀ x, ‖x‖ ≤ 1 → c ≤ ‖u x‖)
    (z : Space n) {f : Space n → ℂ} (hf : Measurable f) (p : ℝ≥0∞) :
    eLpNorm (sparsePiece u R z f) p volume ≤
      ENNReal.ofReal c⁻¹ * eLpNorm ((ball z R).indicator f) p volume := by
  let g := (ball (0 : Space n) R).indicator (fun x ↦ f (x + z))
  have hg : Measurable g := (hf.comp (measurable_id.add_const z)).indicator measurableSet_ball
  have H : eLpNorm (sparsePiece u R z f) p volume ≤ eLpNorm ((c⁻¹ : ℂ) • g) p volume := by
    apply eLpNorm_mono_ae (measurable_sparsePiece u R z hf).aestronglyMeasurable
    filter_upwards [] with x
    simpa only [Pi.smul_apply, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc, g] using norm_sparsePiece_le u hc hR hu z f x
  have he : eLpNorm g p volume = eLpNorm ((ball z R).indicator f) p volume := by
    have htranslate : g = ((ball z R).indicator f) ∘ (fun x ↦ x + z) := by
      funext x
      exact sparsePiece_indicator_translate R z f x
    rw [htranslate]
    exact eLpNorm_comp_measurePreserving (hf.indicator measurableSet_ball).aestronglyMeasurable
      (measurePreserving_add_right volume z)
  rw [eLpNorm_const_smul, ← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc, he] at H
  exact H

end OAI.Analysis.Fourier.Restriction
