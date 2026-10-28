import OAI.Analysis.Fourier.Restriction.ProductNorm

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem lintegral_Icc_add_right {F : ℝ → ℝ≥0∞} (hF : Measurable F) (a b d : ℝ) :
    (∫⁻ t in Icc a b, F (t + d)) = ∫⁻ t in Icc (a + d) (b + d), F t := by
  have H := (measurePreserving_add_right (volume : Measure ℝ) d).setLIntegral_comp_preimage
    (s := Icc (a + d) (b + d)) measurableSet_Icc hF
  have he : (fun t : ℝ ↦ t + d) ⁻¹' Icc (a + d) (b + d) = Icc a b := by
    ext t
    simp only [mem_preimage, mem_Icc, add_le_add_iff_right]
  simpa only [he] using H

theorem lintegral_shifted_radial_annulus_le {n : ℕ} (hn : 1 ≤ n)
    {F : Space n → ℝ≥0∞} (hF : Measurable F) {a : ℝ} (ha : 0 < a) (b : ℝ)
    {d : ℝ} (hd : 0 ≤ d) :
    (∫⁻ ω, ∫⁻ t in Icc a b, F ((t + d) • ω) ∂volume ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      (ENNReal.ofReal (a ^ (n - 1)))⁻¹ * ∫⁻ x, F x := by
  calc
    _ = ∫⁻ ω, ∫⁻ t in Icc (a + d) (b + d), F (t • ω) ∂volume ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
      apply lintegral_congr
      intro ω
      exact lintegral_Icc_add_right (F := fun t : ℝ ↦ F (t • ω)) (by fun_prop) a b d
    _ ≤ ∫⁻ ω, ∫⁻ t in Icc a (b + d), F (t • ω) ∂volume ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
      apply lintegral_mono
      intro ω
      apply lintegral_mono_set
      intro t ht
      exact ⟨by linarith [ht.1], ht.2⟩
    _ ≤ _ := lintegral_radial_annulus_le hn hF ha (b + d)

theorem eLpNorm_shifted_radial_annulus_le {n : ℕ} (hn : 1 ≤ n)
    {f : Space n → ℂ} (hf : Measurable f) {p : ℝ} (hp : 0 < p)
    {a : ℝ} (ha : 0 < a) (b : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    eLpNorm (fun z : Space n × ℝ ↦ f ((z.2 + d) • z.1)) (ENNReal.ofReal p)
      ((OAI.Analysis.Fourier.Restriction.sphereMeasure n).prod (volume.restrict (Icc a b))) ≤
    ((ENNReal.ofReal (a ^ (n - 1)))⁻¹) ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hm : Measurable (fun z : Space n × ℝ ↦ f ((z.2 + d) • z.1)) := by fun_prop
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hm.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le, lintegral_prod _ (by fun_prop)]
  have H := lintegral_shifted_radial_annulus_le hn (hf.enorm.pow_const p) ha b hd
  have H' := ENNReal.rpow_le_rpow H (one_div_nonneg.mpr hp.le)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le)] using H'

end OAI.Analysis.Fourier.Restriction
