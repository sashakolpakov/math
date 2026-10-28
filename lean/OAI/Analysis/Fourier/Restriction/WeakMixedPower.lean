import OAI.Analysis.Fourier.Restriction.WeakMixed
import OAI.Analysis.Fourier.Restriction.MixedPowers

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- The power-form weak mixed extension estimate obtained from a diagonal
estimate, with the exact exponent dictated by the spherical restriction range. -/
theorem sphericalExtension_weak_mixed {n : ℕ} {a s : ℝ}
    (ha : 1 < a) (has : a ≤ s) {C : ℝ≥0∞}
    (hdiag : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal s) volume ≤
        C * eLpNorm g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    {g : Space n → ℂ} (hgm : Measurable g) (hgi : Integrable g (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    (hgn : (∫⁻ ω, ‖g ω‖ₑ ^ a ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    volume {x | 2 * t < ‖OAI.Analysis.Fourier.Restriction.sphericalExtension g x‖} ≤
      C ^ s * ENNReal.ofReal (t ^ (-(a * (s - 1) / (a - 1)))) := by
  calc
    _ = volume {x | 2 * mixedThreshold a t ^ (1 - a) < ‖OAI.Analysis.Fourier.Restriction.sphericalExtension g x‖} := by
      rw [mixedThreshold_power ha ht]
    _ ≤ (C ^ s * ENNReal.ofReal (mixedThreshold a t ^ (s - a))) /
        ENNReal.ofReal (mixedThreshold a t ^ (1 - a)) ^ s :=
      sphericalExtension_weak_mixed_parameter ha has hdiag hgm hgi hgn
        (mixedThreshold_pos ht)
    _ = C ^ s * (ENNReal.ofReal (mixedThreshold a t ^ (s - a)) /
        ENNReal.ofReal (mixedThreshold a t ^ (1 - a)) ^ s) := by
      simp only [div_eq_mul_inv, mul_assoc]
    _ = _ := by rw [mixedThreshold_ratio ha (by linarith : 0 ≤ s) ht]

end OAI.Analysis.Fourier.Restriction
