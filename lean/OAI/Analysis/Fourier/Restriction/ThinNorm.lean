import OAI.Analysis.Fourier.Restriction.Thickening
import OAI.Analysis.Fourier.BochnerRiesz.Product

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem sphere_thickening_norm {n : ℕ} (hn : 1 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      ∀ (F : Space n → ℂ), Measurable F → ∀ p : ℝ, 0 < p → ∀ B : ℝ≥0∞,
      (∀ v : Space n, eLpNorm (fun ω ↦ F (ω + v)) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤ B) →
      eLpNorm F (ENNReal.ofReal p) (volume.restrict (sphericalAnnulus δ)) ≤
        ((ENNReal.ofReal (c * δ ^ (n - 1)))⁻¹ * volume (ball (0 : Space n) (2 * δ))) ^ (1 / p) * B := by
  obtain ⟨c, hc, HC⟩ := sphere_thickening_energy hn
  refine ⟨c, hc, ?_⟩
  intro δ hδ hδhalf F hF p hp B hB
  have H := HC δ hδ hδhalf (fun ξ ↦ ‖F ξ‖ₑ ^ p) (hF.enorm.pow_const p)
  have Hup : (∫⁻ v in ball (0 : Space n) (2 * δ), ∫⁻ ω, ‖F (ω + v)‖ₑ ^ p ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      B ^ p * volume (ball (0 : Space n) (2 * δ)) := by
    calc
      _ ≤ ∫⁻ _v in ball (0 : Space n) (2 * δ), B ^ p := by
        apply lintegral_mono
        intro v
        change (∫⁻ ω, ‖F (ω + v)‖ₑ ^ p ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤ B ^ p
        have hm : AEStronglyMeasurable (fun ω ↦ F (ω + v)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
          (hF.comp (measurable_id.add_const v)).aestronglyMeasurable
        rw [OAI.Analysis.Fourier.BochnerRiesz.lintegral_enorm_rpow_eq_eLpNorm_pow hm hp]
        exact ENNReal.rpow_le_rpow (hB v) hp.le
      _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]
  have hA0 : ENNReal.ofReal (c * δ ^ (n - 1)) ≠ 0 := by positivity
  have HI : (∫⁻ ξ in sphericalAnnulus δ, ‖F ξ‖ₑ ^ p) ≤
      ((ENNReal.ofReal (c * δ ^ (n - 1)))⁻¹ * volume (ball (0 : Space n) (2 * δ))) * B ^ p := by
    calc
      _ = (ENNReal.ofReal (c * δ ^ (n - 1)))⁻¹ *
          (ENNReal.ofReal (c * δ ^ (n - 1)) * (∫⁻ ξ in sphericalAnnulus δ, ‖F ξ‖ₑ ^ p)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hA0 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ (ENNReal.ofReal (c * δ ^ (n - 1)))⁻¹ *
          (B ^ p * volume (ball (0 : Space n) (2 * δ))) := mul_le_mul' le_rfl (H.trans Hup)
      _ = _ := by ring
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
    hF.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  calc
    _ ≤ (((ENNReal.ofReal (c * δ ^ (n - 1)))⁻¹ * volume (ball (0 : Space n) (2 * δ))) * B ^ p) ^ (1 / p) :=
      ENNReal.rpow_le_rpow HI (by positivity)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
        mul_one_div_cancel hp.ne', ENNReal.rpow_one]

end OAI.Analysis.Fourier.Restriction
