import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Scale

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation

def infinityInterpolationConstant (q p : ℝ) : ℝ≥0∞ :=
  2 * (.ofReal (p / (p - q))) ^ (1 / p)

theorem infinityInterpolationConstant_ne_top {q p : ℝ} (hp : 0 < p) :
    infinityInterpolationConstant q p ≠ ⊤ := by
  exact ENNReal.mul_ne_top (by norm_num) (ENNReal.rpow_ne_top_of_nonneg
    (by positivity) ENNReal.ofReal_ne_top)

/-- Strong finite/infinity interpolation, with the exact powers of both
endpoint bounds. -/
theorem operator_finite_infinity_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y)
    (T : (X → ℂ) → Y → ℂ)
    (hTm : ∀ g, Measurable g → Integrable g μ → Measurable (T g))
    (hadd : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      T (fun x => g x + h x) y = T g y + T h y)
    {q p A B : ℝ} (hq : 0 < q) (hqp : q < p) (hA : 0 < A) (hB : 0 < B)
    (hbound : ∀ g, Measurable g → Integrable g μ → MemLp g (.ofReal q) μ →
      eLpNorm (T g) (.ofReal q) ν ≤ .ofReal A * eLpNorm g (.ofReal q) μ)
    (hinf : ∀ g, Measurable g → Integrable g μ → ∀ t : ℝ, 0 < t →
      (∀ x, ‖g x‖ ≤ t) → ∀ᵐ y ∂ν, ‖T g y‖ ≤ B * t)
    {f : X → ℂ} (hf : Measurable f) (hfi : Integrable f μ) (hfq : MemLp f (.ofReal q) μ) :
    eLpNorm (T f) (.ofReal p) ν ≤ infinityInterpolationConstant q p *
      .ofReal (A ^ (q / p) * B ^ (1 - q / p)) * eLpNorm f (.ofReal p) μ := by
  let S : (X → ℂ) → Y → ℂ := fun g => B⁻¹ • T g
  have hSm : ∀ g, Measurable g → Integrable g μ → Measurable (S g) :=
    fun g hg hi => (hTm g hg hi).const_smul _
  have hSa : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      S (fun x => g x + h x) y = S g y + S h y := by
    intro g h hg hh y
    change B⁻¹ • T (fun x => g x + h x) y = B⁻¹ • T g y + B⁻¹ • T h y
    rw [hadd g h hg hh, smul_add]
  have hSb : ∀ g, Measurable g → Integrable g μ → MemLp g (.ofReal q) μ →
      (∫⁻ y, ‖S g y‖ₑ ^ q ∂ν) ≤ (.ofReal (B⁻¹ * A)) ^ q * ∫⁻ x, ‖g x‖ₑ ^ q ∂μ := by
    intro g hg hi hqg
    apply moment_le_of_norm_le μ ν hg (hSm g hg hi) hq
    have H := norm_real_normalized_le ν (T g) (.ofReal q) hB (hbound g hg hi hqg)
    simpa only [S, ENNReal.ofReal_mul (inv_nonneg.mpr hB.le),
      ENNReal.ofReal_inv_of_pos hB] using H
  have hSi : ∀ g, Measurable g → Integrable g μ → ∀ t : ℝ, 0 < t →
      (∀ x, ‖g x‖ ≤ t) → ∀ᵐ y ∂ν, ‖S g y‖ ≤ t := by
    intro g hg hi t ht hb
    filter_upwards [hinf g hg hi t ht hb] with y hy
    change ‖B⁻¹ • T g y‖ ≤ t
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)]
    calc
      _ ≤ B⁻¹ * (B * t) := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hB.le)
      _ = t := by field_simp
  have H := operator_infinity_moment_bound μ ν S hSm hSa hq hqp hSb hSi hf hfi hfq
  rw [norm_restore_real_scale ν (T f) (.ofReal p) hB]
  refine (mul_le_mul' (le_refl (.ofReal B)) H).trans_eq ?_
  have hp : 0 < p := hq.trans hqp
  have hc : B * (B⁻¹ * A) ^ (q / p) = A ^ (q / p) * B ^ (1 - q / p) := by
    rw [Real.mul_rpow (inv_nonneg.mpr hB.le) hA.le, Real.inv_rpow hB.le,
      Real.rpow_sub hB]
    simp only [Real.rpow_one]
    ring
  rw [ENNReal.mul_rpow_of_nonneg _ _ (show 0 ≤ 1 / p by positivity),
    ← ENNReal.rpow_mul]
  rw [show q * (1 / p) = q / p by ring]
  rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (inv_nonneg.mpr hB.le) hA.le)
    (div_nonneg hq.le hp.le)]
  unfold infinityInterpolationConstant
  rw [show .ofReal B * (2 * (.ofReal ((B⁻¹ * A) ^ (q / p)) *
      (.ofReal (p / (p - q))) ^ (1 / p)) * eLpNorm f (.ofReal p) μ) =
      (2 * (.ofReal (p / (p - q))) ^ (1 / p)) *
        (.ofReal B * .ofReal ((B⁻¹ * A) ^ (q / p))) * eLpNorm f (.ofReal p) μ by ring]
  rw [← ENNReal.ofReal_mul hB.le, hc]

end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
