import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Infinity

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation


theorem moment_le_of_norm_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {f : X → ℂ} {g : Y → ℂ}
    (hf : Measurable f) (hg : Measurable g) {q : ℝ} (hq : 0 < q) {A : ℝ≥0∞}
    (hb : eLpNorm g (.ofReal q) ν ≤ A * eLpNorm f (.ofReal q) μ) :
    (∫⁻ y, ‖g y‖ₑ ^ q ∂ν) ≤ A ^ q * ∫⁻ x, ‖f x‖ₑ ^ q ∂μ := by
  have H := ENNReal.rpow_le_rpow hb hq.le
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ hq.le,
    OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hq hf.aestronglyMeasurable,
    OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hq hg.aestronglyMeasurable] using H

theorem norm_real_normalized_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) (p : ℝ≥0∞) {M : ℝ} (hM : 0 < M)
    {A N : ℝ≥0∞} (hf : eLpNorm f p μ ≤ A * N) :
    eLpNorm (M⁻¹ • f) p μ ≤ (.ofReal M)⁻¹ * A * N := by
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (inv_nonneg.mpr hM.le),
    ENNReal.ofReal_inv_of_pos hM]
  exact (mul_le_mul' le_rfl hf).trans_eq (mul_assoc _ _ _).symm

theorem norm_restore_real_scale {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) (p : ℝ≥0∞) {M : ℝ} (hM : 0 < M) :
    eLpNorm f p μ = .ofReal M * eLpNorm (M⁻¹ • f) p μ := by
  have he : f = M • (M⁻¹ • f) := by simp [smul_smul, hM.ne']
  conv_lhs => rw [he]
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hM.le]

def finiteInterpolationConstant (q₀ p q₁ : ℝ) : ℝ≥0∞ :=
  2 * (.ofReal (p / (p - q₀)) + .ofReal (p / (q₁ - p))) ^ (1 / p)

theorem finiteInterpolationConstant_ne_top {q₀ p q₁ : ℝ} (hp : 0 < p) :
    finiteInterpolationConstant q₀ p q₁ ≠ ⊤ := by
  exact ENNReal.mul_ne_top (by norm_num) (ENNReal.rpow_ne_top_of_nonneg
    (by positivity) (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,ENNReal.ofReal_ne_top⟩))

/-- Two finite strong endpoints with a common bound retain that bound linearly. -/
theorem operator_common_endpoint_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y)
    (T : (X → ℂ) → Y → ℂ)
    (hTm : ∀ g, Measurable g → Integrable g μ → Measurable (T g))
    (hadd : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      T (fun x => g x + h x) y = T g y + T h y)
    {q₀ p q₁ M : ℝ} (hq₀ : 0 < q₀) (h0p : q₀ < p) (hp1 : p < q₁) (hM : 0 < M)
    (hbound₀ : ∀ g, Measurable g → Integrable g μ → MemLp g (.ofReal q₀) μ →
      MemLp g (.ofReal q₁) μ → eLpNorm (T g) (.ofReal q₀) ν ≤ .ofReal M * eLpNorm g (.ofReal q₀) μ)
    (hbound₁ : ∀ g, Measurable g → Integrable g μ → MemLp g (.ofReal q₀) μ →
      MemLp g (.ofReal q₁) μ → eLpNorm (T g) (.ofReal q₁) ν ≤ .ofReal M * eLpNorm g (.ofReal q₁) μ)
    {f : X → ℂ} (hf : Measurable f) (hfi : Integrable f μ)
    (hf₀ : MemLp f (.ofReal q₀) μ) (hf₁ : MemLp f (.ofReal q₁) μ) :
    eLpNorm (T f) (.ofReal p) ν ≤
      finiteInterpolationConstant q₀ p q₁ * .ofReal M * eLpNorm f (.ofReal p) μ := by
  let S : (X → ℂ) → Y → ℂ := fun g => M⁻¹ • T g
  have hSm : ∀ g, Measurable g → Integrable g μ → Measurable (S g) :=
    fun g hg hi => (hTm g hg hi).const_smul _
  have hSa : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      S (fun x => g x + h x) y = S g y + S h y := by
    intro g h hg hh y
    change M⁻¹ • T (fun x => g x + h x) y = M⁻¹ • T g y + M⁻¹ • T h y
    rw [hadd g h hg hh, smul_add]
  have hn {q : ℝ} {g : X → ℂ}
      (hb : eLpNorm (T g) (.ofReal q) ν ≤ .ofReal M * eLpNorm g (.ofReal q) μ) :
      eLpNorm (S g) (.ofReal q) ν ≤ 1 * eLpNorm g (.ofReal q) μ := by
    exact (norm_real_normalized_le ν (T g) (.ofReal q) hM hb).trans_eq (by
      rw [ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top])
  have H := operator_two_moment_bound μ ν S hSm hSa hq₀ h0p hp1
    (A := 1) (B := 1)
    (fun g hg hi h0 h1 => by
      simpa only [ENNReal.one_rpow] using (moment_le_of_norm_le μ ν hg (hSm g hg hi)
        hq₀ (hn (hbound₀ g hg hi h0 h1))))
    (fun g hg hi h0 h1 => by
      simpa only [ENNReal.one_rpow] using (moment_le_of_norm_le μ ν hg (hSm g hg hi)
        (hq₀.trans (h0p.trans hp1)) (hn (hbound₁ g hg hi h0 h1))))
    hf hfi hf₀ hf₁
  rw [norm_restore_real_scale ν (T f) (.ofReal p) hM]
  have H' := mul_le_mul' (le_refl (.ofReal M)) H
  simpa only [S, one_mul, finiteInterpolationConstant] using H'.trans_eq (by ring_nf)

end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
