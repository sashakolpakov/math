import OAI.Analysis.Fourier.BochnerRiesz.TimeHolder
import OAI.Analysis.Fourier.SquareFunction.Shell

open OAI.Analysis.Fourier.Wave

/-! Weighted time integration into a spatial square norm. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory
open scoped ENNReal

theorem eLpNorm_of_weighted_time_square_domination {n : ℕ} {p : ℝ} (hp : 2 ≤ p)
    {κ : ℝ → ℝ≥0∞} (hκ : Measurable κ) (hκone : ∀ t, κ t ≤ 1)
    {F : Space n × ℝ → ℂ} (hF : Measurable F) {T : Space n → ℝ}
    (hT : AEStronglyMeasurable T volume) {A : ℝ≥0∞}
    (hdom : ∀ x, ‖T x‖ₑ ^ (2 : ℝ) ≤ A ^ (2 : ℝ) * ∫⁻ t : ℝ, κ t * ‖F (x, t)‖ₑ ^ (2 : ℝ)) :
    eLpNorm T (ENNReal.ofReal p) volume ≤
      A * (∫⁻ t : ℝ, κ t) ^ (1 / 2 - 1 / p) *
        eLpNorm F (ENNReal.ofReal p) (volume.prod volume) := by
  have hp0 : 0 < p := by linarith
  have hhalf : 0 ≤ p / 2 := by positivity
  have hp2 : (2 : ℝ) * (p / 2) = p := by ring
  have hpoint (x : Space n) : ‖T x‖ₑ ^ p ≤
      (A ^ p * (∫⁻ t : ℝ, κ t) ^ (p / 2 - 1)) *
        ∫⁻ t : ℝ, κ t * ‖F (x, t)‖ₑ ^ p := by
    calc
      _ = (‖T x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by rw [← ENNReal.rpow_mul, hp2]
      _ ≤ (A ^ (2 : ℝ) * ∫⁻ t : ℝ, κ t * ‖F (x, t)‖ₑ ^ (2 : ℝ)) ^ (p / 2) :=
        ENNReal.rpow_le_rpow (hdom x) hhalf
      _ = A ^ p * (∫⁻ t : ℝ, κ t * ‖F (x, t)‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hhalf, ← ENNReal.rpow_mul, hp2]
      _ ≤ A ^ p * ((∫⁻ t : ℝ, κ t) ^ (p / 2 - 1) *
          ∫⁻ t : ℝ, κ t * (‖F (x, t)‖ₑ ^ (2 : ℝ)) ^ (p / 2)) := by
        apply mul_le_mul' le_rfl
        exact OAI.Analysis.Fourier.WavePackets.lintegral_weighted_rpow_le hκ
          ((hF.comp (measurable_const.prodMk measurable_id)).enorm.pow_const 2) (by linarith)
      _ = _ := by simp only [← ENNReal.rpow_mul, hp2, mul_assoc]
  have hi : (∫⁻ x : Space n, ‖T x‖ₑ ^ p) ≤
      (A ^ p * (∫⁻ t : ℝ, κ t) ^ (p / 2 - 1)) *
        ∫⁻ z : Space n × ℝ, ‖F z‖ₑ ^ p ∂volume.prod volume := by
    calc
      _ ≤ ∫⁻ x : Space n, (A ^ p * (∫⁻ t : ℝ, κ t) ^ (p / 2 - 1)) *
          ∫⁻ t : ℝ, κ t * ‖F (x, t)‖ₑ ^ p := lintegral_mono hpoint
      _ = (A ^ p * (∫⁻ t : ℝ, κ t) ^ (p / 2 - 1)) *
          ∫⁻ x : Space n, ∫⁻ t : ℝ, κ t * ‖F (x, t)‖ₑ ^ p := by
        apply lintegral_const_mul''
        exact ((hκ.comp measurable_snd).mul (hF.enorm.pow_const p)).lintegral_prod_right.aemeasurable
      _ ≤ (A ^ p * (∫⁻ t : ℝ, κ t) ^ (p / 2 - 1)) *
          ∫⁻ x : Space n, ∫⁻ t : ℝ, ‖F (x, t)‖ₑ ^ p := by
        apply mul_le_mul' le_rfl
        apply lintegral_mono
        intro x
        apply lintegral_mono
        intro t
        simpa only [one_mul] using mul_le_mul' (hκone t) (le_refl (‖F (x, t)‖ₑ ^ p))
      _ = _ := by rw [lintegral_prod _ (hF.enorm.pow_const p).aemeasurable]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hT,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hF.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  calc
    _ ≤ ((A ^ p * (∫⁻ t : ℝ, κ t) ^ (p / 2 - 1)) *
        ∫⁻ z : Space n × ℝ, ‖F z‖ₑ ^ p ∂volume.prod volume) ^ (1 / p) :=
      ENNReal.rpow_le_rpow hi (by positivity)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one,
        ← ENNReal.rpow_mul]
      congr 2
      field_simp

end OAI.Analysis.Fourier.SquareFunction
