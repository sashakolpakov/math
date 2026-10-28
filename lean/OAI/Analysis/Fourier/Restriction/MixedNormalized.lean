import OAI.Analysis.Fourier.Restriction.WeakMixedPower
import OAI.Analysis.Fourier.Restriction.WeakStrong
import OAI.Analysis.Fourier.Restriction.TruncationL1

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem eLpNorm_le_of_half_moment_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {u : X → ℂ} (hu : Measurable u) {p : ℝ} (hp : 0 < p) {C : ℝ≥0∞}
    (h : (∫⁻ x, ENNReal.ofReal (‖u x‖ / 2) ^ p ∂μ) ≤ C) :
    eLpNorm u (ENNReal.ofReal p) μ ≤ 2 * C ^ (1 / p) := by
  have hm : Measurable (fun x ↦ ENNReal.ofReal (‖u x‖ / 2) ^ p) :=
    (hu.norm.div_const 2).ennreal_ofReal.pow_const p
  have H : eLpNorm u (ENNReal.ofReal p) μ ^ p ≤ (2 : ℝ≥0∞) ^ p * C := by
    rw [OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp hu.aestronglyMeasurable]
    calc
      _ = ∫⁻ x, (2 : ℝ≥0∞) ^ p * ENNReal.ofReal (‖u x‖ / 2) ^ p ∂μ := by
        apply lintegral_congr
        intro x
        have hx : ENNReal.ofReal ‖u x‖ = ENNReal.ofReal (2 : ℝ) *
            ENNReal.ofReal (‖u x‖ / 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring
        rw [ofReal_norm, ENNReal.ofReal_ofNat] at hx
        rw [hx, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
      _ = (2 : ℝ≥0∞) ^ p * ∫⁻ x, ENNReal.ofReal (‖u x‖ / 2) ^ p ∂μ :=
        lintegral_const_mul _ hm
      _ ≤ _ := by gcongr
  have H' := ENNReal.rpow_le_rpow H (le_of_lt (one_div_pos.mpr hp))
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt (one_div_pos.mpr hp)),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one] using H'

def mixedExtensionConstant (n : ℕ) (a s b : ℝ) (C : ℝ≥0∞) : ℝ≥0∞ :=
  2 * (C ^ s * ENNReal.ofReal
    (b * (((OAI.Analysis.Fourier.Restriction.sphereMeasure n univ).toReal + 1) ^ (b - a * (s - 1) / (a - 1)) /
      (b - a * (s - 1) / (a - 1))))) ^ (1 / b)

theorem mixedExtensionConstant_ne_top {n : ℕ} {a s b : ℝ} {C : ℝ≥0∞}
    (hs : 0 ≤ s) (hb : 0 < b) (hC : C ≠ ⊤) :
    mixedExtensionConstant n a s b C ≠ ⊤ := by
  unfold mixedExtensionConstant
  apply ENNReal.mul_ne_top (by norm_num)
  apply ne_of_lt
  apply ENNReal.rpow_lt_top_of_nonneg (le_of_lt (one_div_pos.mpr hb))
  exact ENNReal.mul_ne_top (ne_of_lt (ENNReal.rpow_lt_top_of_nonneg hs hC))
    ENNReal.ofReal_ne_top

/-- Every diagonal extension bound gives the strict mixed bounds above its
interpolation line, initially for normalized measurable inputs. -/
theorem sphericalExtension_mixed_normalized {n : ℕ} {a s b : ℝ}
    (ha : 1 < a) (has : a ≤ s) (hb : 0 < b)
    (hab : a * (s - 1) / (a - 1) < b) {C : ℝ≥0∞}
    (hdiag : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal s) volume ≤
        C * eLpNorm g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    {g : Space n → ℂ} (hgm : Measurable g) (hgi : Integrable g (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    (hgn : (∫⁻ ω, ‖g ω‖ₑ ^ a ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤ 1) :
    eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal b) volume ≤
      mixedExtensionConstant n a s b C := by
  have hEm := (continuous_sphericalExtension hgi).measurable
  have H := lintegral_power_le_of_weak_and_bounded volume
    (hEm.norm.div_const 2) (fun x ↦ div_nonneg (norm_nonneg _) (by norm_num))
    (show 0 ≤ (OAI.Analysis.Fourier.Restriction.sphereMeasure n univ).toReal + 1 by positivity)
    (fun x ↦ by
      have hx := norm_sphericalExtension_le_of_normalized_moment hgm ha.le hgn x
      have hn := norm_nonneg (OAI.Analysis.Fourier.Restriction.sphericalExtension g x)
      linarith) hb hab (A := C ^ s) (fun t ht ↦ by
      have he : {x | t < ‖OAI.Analysis.Fourier.Restriction.sphericalExtension g x‖ / 2} =
          {x | 2 * t < ‖OAI.Analysis.Fourier.Restriction.sphericalExtension g x‖} := by
        ext x
        simp only [Set.mem_ofPred_eq]
        constructor <;> intro hx <;> linarith
      rw [he]
      exact sphericalExtension_weak_mixed ha has hdiag hgm hgi hgn ht)
  exact eLpNorm_le_of_half_moment_bound volume hEm hb H

end OAI.Analysis.Fourier.Restriction
