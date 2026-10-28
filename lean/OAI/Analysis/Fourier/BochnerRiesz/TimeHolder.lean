import OAI.Analysis.Fourier.BochnerRiesz.Product
import OAI.Analysis.Fourier.WavePackets.Young

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

/-- Weighted time integration maps a space-time `Lᵖ` bound to a spatial
`Lᵖ` bound. The dominating time density may be chosen once for every
radius of a thin shell. -/
theorem eLpNorm_of_weighted_time_domination {E : Type*} [TopologicalSpace E] [ENorm E]
    {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    {κ : ℝ → ℝ≥0∞} (hκ : Measurable κ) (hκone : ∀ t, κ t ≤ 1)
    {F : Space n × ℝ → ℂ} (hF : Measurable F) {T : Space n → E}
    (hT : AEStronglyMeasurable T volume) {A : ℝ≥0∞}
    (hdom : ∀ x, ‖T x‖ₑ ≤ A * ∫⁻ t : ℝ, κ t * ‖F (x, t)‖ₑ) :
    eLpNorm T (ENNReal.ofReal p) volume ≤
      A * (∫⁻ t : ℝ, κ t) ^ ((p - 1) / p) *
        eLpNorm F (ENNReal.ofReal p) (volume.prod volume) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpoint (x : Space n) : ‖T x‖ₑ ^ p ≤
      (A ^ p * (∫⁻ t : ℝ, κ t) ^ (p - 1)) *
        ∫⁻ t : ℝ, κ t * ‖F (x, t)‖ₑ ^ p := by
    calc
      _ ≤ (A * ∫⁻ t : ℝ, κ t * ‖F (x, t)‖ₑ) ^ p :=
        ENNReal.rpow_le_rpow (hdom x) hp0.le
      _ = A ^ p * (∫⁻ t : ℝ, κ t * ‖F (x, t)‖ₑ) ^ p :=
        ENNReal.mul_rpow_of_nonneg _ _ hp0.le
      _ ≤ A ^ p * ((∫⁻ t : ℝ, κ t) ^ (p - 1) *
          ∫⁻ t : ℝ, κ t * ‖F (x, t)‖ₑ ^ p) := by
        apply mul_le_mul' le_rfl
        exact OAI.Analysis.Fourier.WavePackets.lintegral_weighted_rpow_le hκ
          (hF.comp (measurable_const.prodMk measurable_id)).enorm hp
      _ = _ := (mul_assoc _ _ _).symm
  have hi : (∫⁻ x : Space n, ‖T x‖ₑ ^ p) ≤
      (A ^ p * (∫⁻ t : ℝ, κ t) ^ (p - 1)) *
        ∫⁻ z : Space n × ℝ, ‖F z‖ₑ ^ p ∂volume.prod volume := by
    calc
      _ ≤ ∫⁻ x : Space n, (A ^ p * (∫⁻ t : ℝ, κ t) ^ (p - 1)) *
          ∫⁻ t : ℝ, κ t * ‖F (x, t)‖ₑ ^ p := lintegral_mono hpoint
      _ = (A ^ p * (∫⁻ t : ℝ, κ t) ^ (p - 1)) *
          ∫⁻ x : Space n, ∫⁻ t : ℝ, κ t * ‖F (x, t)‖ₑ ^ p := by
        apply lintegral_const_mul''
        exact ((hκ.comp measurable_snd).mul (hF.enorm.pow_const p)).lintegral_prod_right.aemeasurable
      _ ≤ (A ^ p * (∫⁻ t : ℝ, κ t) ^ (p - 1)) *
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
    _ ≤ ((A ^ p * (∫⁻ t : ℝ, κ t) ^ (p - 1)) *
        ∫⁻ z : Space n × ℝ, ‖F z‖ₑ ^ p ∂volume.prod volume) ^ (1 / p) :=
      ENNReal.rpow_le_rpow hi (by positivity)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one,
        ← ENNReal.rpow_mul]
      congr 2
      simp only [div_eq_mul_inv, one_mul]

end OAI.Analysis.Fourier.BochnerRiesz
