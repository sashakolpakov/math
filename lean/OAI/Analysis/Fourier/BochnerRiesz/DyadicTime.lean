import OAI.Analysis.Fourier.BochnerRiesz.Weighted

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

def smallTimeRadius (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k + 1)
def largeTimeRadius (k : ℕ) : ℝ := (2 : ℝ) ^ k

theorem positive_time_dyadic_cover :
    Ioi (0 : ℝ) ⊆ (⋃ k : ℕ, Icc (smallTimeRadius k) (2 * smallTimeRadius k)) ∪
      (⋃ k : ℕ, Icc (largeTimeRadius k) (2 * largeTimeRadius k)) := by
  intro t ht
  by_cases hone : t ≤ 1
  · obtain ⟨k, hk⟩ := exists_nat_pow_near_of_lt_one ht hone
      (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
    apply Or.inl
    refine mem_iUnion.mpr ⟨k, ?_⟩
    have hid : 2 * smallTimeRadius k = (1 / 2 : ℝ) ^ k := by
      simp only [smallTimeRadius, pow_succ]
      ring
    rw [hid]
    exact ⟨hk.1.le, hk.2⟩
  · obtain ⟨k, hk⟩ := exists_nat_pow_near (le_of_not_ge hone) (show (1 : ℝ) < 2 by norm_num)
    apply Or.inr
    refine mem_iUnion.mpr ⟨k, ?_⟩
    exact ⟨hk.1, by simpa [largeTimeRadius, pow_succ, mul_comm] using hk.2.le⟩

theorem lintegral_positive_le_dyadic (G : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioi (0 : ℝ), G t) ≤
      (∑' k : ℕ, ∫⁻ t in Icc (smallTimeRadius k) (2 * smallTimeRadius k), G t) +
      (∑' k : ℕ, ∫⁻ t in Icc (largeTimeRadius k) (2 * largeTimeRadius k), G t) := by
  exact (lintegral_mono_set positive_time_dyadic_cover).trans
    ((lintegral_union_le _ _ _).trans (add_le_add (lintegral_iUnion_le _ _) (lintegral_iUnion_le _ _)))

theorem dyadic_time_moment_bound (G : ℝ → ℝ≥0∞) (B a : ℝ≥0∞)
    (hsmall : ∀ k : ℕ, (∫⁻ t in Icc (smallTimeRadius k) (2 * smallTimeRadius k), G t) ≤
      B * (1 / 2 : ℝ≥0∞) ^ (k + 1))
    (hlarge : ∀ k : ℕ, (∫⁻ t in Icc (largeTimeRadius k) (2 * largeTimeRadius k), G t) ≤ B * a ^ k) :
    (∫⁻ t in Ioi (0 : ℝ), G t) ≤
      B * ((∑' k : ℕ, (1 / 2 : ℝ≥0∞) ^ (k + 1)) + (∑' k : ℕ, a ^ k)) := by
  refine (lintegral_positive_le_dyadic G).trans ?_
  calc
    _ ≤ (∑' k : ℕ, B * (1 / 2 : ℝ≥0∞) ^ (k + 1)) + (∑' k : ℕ, B * a ^ k) :=
      add_le_add (ENNReal.tsum_le_tsum hsmall) (ENNReal.tsum_le_tsum hlarge)
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, mul_add]

theorem time_section_moment_eq {n : ℕ} {F : Space n × ℝ → ℂ} (hF : Continuous F)
    {ν : Measure ℝ} [SFinite ν] {p : ℝ} (hp : 0 < p) :
    (∫⁻ t, ∫⁻ x : Space n, ‖F (x, t)‖ₑ ^ p ∂volume ∂ν) =
      eLpNorm F (ENNReal.ofReal p) (volume.prod ν) ^ p := by
  rw [← lintegral_prod_symm _ (hF.measurable.enorm.aemeasurable.pow_const p)]
  exact lintegral_enorm_rpow_eq_eLpNorm_pow hF.aestronglyMeasurable hp

theorem slab_moment_of_norm_bound {n : ℕ} {F : Space n × ℝ → ℂ} (hF : Continuous F)
    {p r e : ℝ} (hp : 0 < p) (hr : 0 < r) {B : ℝ≥0∞}
    (hb : eLpNorm F (ENNReal.ofReal p) (timeSlabMeasure n r) ≤ ENNReal.ofReal (r ^ e) * B) :
    (∫⁻ t in Icc r (2 * r), ∫⁻ x : Space n, ‖F (x, t)‖ₑ ^ p) ≤
      ENNReal.ofReal (r ^ (e * p)) * B ^ p := by
  rw [time_section_moment_eq hF hp]
  calc
    _ ≤ (ENNReal.ofReal (r ^ e) * B) ^ p := ENNReal.rpow_le_rpow hb hp.le
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le,
        ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hr e), ← Real.rpow_mul hr.le]

theorem dyadic_norm_bounds_imply_positive_moment {n : ℕ} {F : Space n × ℝ → ℂ}
    (hF : Continuous F) {p : ℝ} (hp : 0 < p) (e : ℝ) (B : ℝ≥0∞)
    (hsmall : ∀ k : ℕ, eLpNorm F (ENNReal.ofReal p) (timeSlabMeasure n (smallTimeRadius k)) ≤
      ENNReal.ofReal ((smallTimeRadius k) ^ (1 / p)) * B)
    (hlarge : ∀ k : ℕ, eLpNorm F (ENNReal.ofReal p) (timeSlabMeasure n (largeTimeRadius k)) ≤
      ENNReal.ofReal ((largeTimeRadius k) ^ e) * B) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Space n, ‖F (x, t)‖ₑ ^ p) ≤
      B ^ p * ((∑' k : ℕ, (1 / 2 : ℝ≥0∞) ^ (k + 1)) +
        (∑' k : ℕ, (ENNReal.ofReal (2 ^ (e * p))) ^ k)) := by
  apply dyadic_time_moment_bound
  · intro k
    have hr : 0 < smallTimeRadius k := by unfold smallTimeRadius; positivity
    have H := slab_moment_of_norm_bound hF hp hr (hsmall k)
    rw [one_div_mul_cancel hp.ne', Real.rpow_one] at H
    have hc : ENNReal.ofReal (smallTimeRadius k) = (1 / 2 : ℝ≥0∞) ^ (k + 1) := by
      rw [smallTimeRadius, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hc] at H
    simpa only [mul_comm] using H
  · intro k
    have hr : 0 < largeTimeRadius k := by unfold largeTimeRadius; positivity
    have H := slab_moment_of_norm_bound hF hp hr (hlarge k)
    have heq : (largeTimeRadius k) ^ (e * p) = (2 ^ (e * p) : ℝ) ^ k := by
      rw [largeTimeRadius, ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
        mul_comm (k : ℝ), Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    rw [heq, ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 ^ (e * p))] at H
    simpa only [mul_comm] using H

end OAI.Analysis.Fourier.BochnerRiesz
