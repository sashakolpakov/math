import OAI.Analysis.Fourier.Restriction.FourierAmplitude
import OAI.Analysis.Fourier.Restriction.Markov

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- A bounded-input Fourier restriction estimate. The exponent `p` controls
the input support size and `q` is the actual sphere norm exponent. -/
def RestrictedFourierBound (n : ℕ) (p : ℝ) (q C : ℝ≥0∞) : Prop :=
  ∀ E : Set (Space n), MeasurableSet E → volume E ≠ ⊤ →
    ∀ f : Space n → ℂ, Measurable f → Integrable f →
      (∀ x, ‖f x‖ ≤ 1) → (∀ x, x ∉ E → f x = 0) →
        eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) q (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤ C * (volume E) ^ (1 / p)

/-- The bounded-input estimate applied to one amplitude band. -/
theorem restrictedFourierBound_amplitudeBand {n : ℕ} {r p : ℝ} {q C : ℝ≥0∞}
    (hr : 0 < r) (hp : 0 < p) (hres : RestrictedFourierBound n r q C)
    {f : Space n → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (hfn : (∫⁻ x, ‖f x‖ₑ ^ p) ≤ 1) {l u : ℝ} (hl : 0 < l) (hu : 0 < u) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (amplitudeBand f l u)) q (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      C * ENNReal.ofReal (u * l ^ (-p / r)) := by
  let E : Set (Space n) := {x | l < ‖f x‖}
  have hEm : MeasurableSet E := measurableSet_lt measurable_const hf.norm
  have hE : volume E ≤ 1 / ENNReal.ofReal l ^ p := by
    exact (measure_norm_gt_le_moment volume hf hp hl).trans (by gcongr)
  have hEt : volume E ≠ ⊤ := ne_of_lt (hE.trans_lt (by
    apply ENNReal.div_lt_top ENNReal.one_ne_top
    exact ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hl) ENNReal.ofReal_ne_top)))
  let g : Space n → ℂ := (u : ℂ)⁻¹ • amplitudeBand f l u
  have hgm : Measurable g := (measurable_amplitudeBand hf l u).const_smul _
  have hgi : Integrable g := (integrable_amplitudeBand hf hfi l u).const_mul _
  have hgb : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    change ‖(u : ℂ)⁻¹ * amplitudeBand f l u x‖ ≤ 1
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
    calc
      _ ≤ u⁻¹ * u := mul_le_mul_of_nonneg_left (norm_amplitudeBand_le_upper f l hu.le x) (inv_nonneg.mpr hu.le)
      _ = 1 := inv_mul_cancel₀ hu.ne'
  have hgs : ∀ x, x ∉ E → g x = 0 := by
    intro x hx
    change (u : ℂ)⁻¹ * amplitudeBand f l u x = 0
    rw [amplitudeBand_eq_zero_of_le f l u (le_of_not_gt hx), mul_zero]
  have H := hres E hEm hEt g hgm hgi hgb hgs
  have hrestore : amplitudeBand f l u = (u : ℂ) • g := by
    funext x
    change amplitudeBand f l u x = (u : ℂ) * ((u : ℂ)⁻¹ * amplitudeBand f l u x)
    rw [← mul_assoc, mul_inv_cancel₀ (show (u : ℂ) ≠ 0 by exact_mod_cast hu.ne'), one_mul]
  have hFrestore : OAI.Analysis.Fourier.LocalSmoothing.angularFourier (amplitudeBand f l u) = (u : ℂ) • OAI.Analysis.Fourier.LocalSmoothing.angularFourier g := by
    funext ξ
    calc
      _ = OAI.Analysis.Fourier.LocalSmoothing.angularFourier ((u : ℂ) • g) ξ := congrArg (fun f ↦ OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) hrestore
      _ = _ := angularFourier_const_mul (u : ℂ) g ξ
  have hunorm : ‖(u : ℂ)‖ₑ = ENNReal.ofReal u := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  have he : (1 / ENNReal.ofReal l ^ p) ^ (1 / r) = ENNReal.ofReal (l ^ (-p / r)) := by
    rw [one_div, ← ENNReal.rpow_neg, ← ENNReal.rpow_mul]
    have HH : ENNReal.ofReal l ^ (-p * r⁻¹) = ENNReal.ofReal (l ^ (-p * r⁻¹)) :=
      ENNReal.ofReal_rpow_of_pos hl
    simpa only [div_eq_mul_inv, one_mul] using HH
  rw [hFrestore, eLpNorm_const_smul, hunorm]
  calc
    _ ≤ ENNReal.ofReal u * (C * (volume E) ^ (1 / r)) := by gcongr
    _ ≤ ENNReal.ofReal u * (C * (1 / ENNReal.ofReal l ^ p) ^ (1 / r)) := by
      gcongr
    _ = _ := by rw [he, ENNReal.ofReal_mul hu.le]; ring

end OAI.Analysis.Fourier.Restriction
