import OAI.Analysis.Fourier.Restriction.Basic
import OAI.Analysis.Fourier.Restriction.Interpolation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem eLpNorm_le_bound_mul_measure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {g : X → ℂ} (hg : AEStronglyMeasurable g μ)
    {E : Set X} (hE : MeasurableSet E) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ x, ‖g x‖ ≤ A) (hsupport : ∀ x, x ∉ E → g x = 0)
    {p : ℝ} (hp : 0 < p) :
    eLpNorm g (ENNReal.ofReal p) μ ≤ ENNReal.ofReal A * μ E ^ (1 / p) := by
  have hmono : eLpNorm g (ENNReal.ofReal p) μ ≤
      eLpNorm (E.indicator (fun _ ↦ (A : ℂ))) (ENNReal.ofReal p) μ := by
    apply eLpNorm_mono hg
    intro x
    by_cases hx : x ∈ E
    · simpa [hx, Complex.norm_real, abs_of_nonneg hA] using hbound x
    · simp [hx, hsupport x hx]
  calc
    _ ≤ _ := hmono
    _ = ENNReal.ofReal A * μ E ^ (1 / p) := by
      rw [eLpNorm_indicator_const hE.nullMeasurableSet (by positivity) ENNReal.ofReal_ne_top]
      simp [ENNReal.toReal_ofReal hp.le, ← ofReal_norm, Complex.norm_real, abs_of_nonneg hA]

/-- Restricted strong-type estimate from one diagonal extension bound.
The explicit power of the support measure drives the strict mixed-range
dyadic-amplitude summation. -/
theorem sphericalExtension_bounded_input {n : ℕ} {s b : ℝ}
    (hs : 1 < s) (hsb : s ≤ b) {C : ℝ≥0∞}
    (hdiag : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal s) volume ≤
        C * eLpNorm g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    {g : Space n → ℂ} (hg : AEStronglyMeasurable g (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    {E : Set (Space n)} (hE : MeasurableSet E) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ x, ‖g x‖ ≤ A) (hsupport : ∀ x, x ∉ E → g x = 0) :
    eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal b) volume ≤
      C ^ (s / b) * ENNReal.ofReal A *
        (OAI.Analysis.Fourier.Restriction.sphereMeasure n E) ^ ((b - s + 1) / b) := by
  have hs0 : 0 < s := by linarith
  have hb : 0 < b := hs0.trans_le hsb
  have hgs : MemLp g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
    (memLp_top_of_bound hg A (Filter.Eventually.of_forall hbound)).mono_exponent le_top
  have hgi : Integrable g (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
    apply memLp_one_iff_integrable.mp
    exact (memLp_top_of_bound hg A (Filter.Eventually.of_forall hbound)).mono_exponent le_top
  have h1 := eLpNorm_le_bound_mul_measure (OAI.Analysis.Fourier.Restriction.sphereMeasure n) hg hE hA hbound hsupport (p := 1) (by norm_num)
  simp only [ENNReal.ofReal_one, one_div_one, ENNReal.rpow_one] at h1
  have hsn := eLpNorm_le_bound_mul_measure (OAI.Analysis.Fourier.Restriction.sphereMeasure n) hg hE hA hbound hsupport hs0
  have hEg : AEStronglyMeasurable (OAI.Analysis.Fourier.Restriction.sphericalExtension g) volume :=
    (continuous_sphericalExtension hgi).aestronglyMeasurable
  have hpoint : ∀ᵐ x ∂volume, ‖OAI.Analysis.Fourier.Restriction.sphericalExtension g x‖ₑ ≤
      ENNReal.ofReal A * OAI.Analysis.Fourier.Restriction.sphereMeasure n E := by
    filter_upwards [] with x
    exact (enorm_sphericalExtension_le g x).trans (by
      rwa [← eLpNorm_one_eq_lintegral_enorm hg])
  have H := eLpNorm_le_of_enorm_bound volume hEg hs0 hsb hpoint
  calc
    _ ≤ _ := H
    _ ≤ (ENNReal.ofReal A * OAI.Analysis.Fourier.Restriction.sphereMeasure n E) ^ ((b - s) / b) *
        (C * (ENNReal.ofReal A * OAI.Analysis.Fourier.Restriction.sphereMeasure n E ^ (1 / s))) ^ (s / b) := by
      apply mul_le_mul le_rfl _ zero_le zero_le
      apply ENNReal.rpow_le_rpow _ (div_nonneg hs0.le hb.le)
      exact (hdiag g hgs).trans (mul_le_mul le_rfl hsn zero_le zero_le)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg (sub_nonneg.mpr hsb) hb.le),
        ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg hs0.le hb.le),
        ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg hs0.le hb.le),
        ← ENNReal.rpow_mul]
      have hsplit : (b - s) / b + s / b = 1 := by field_simp ; ring
      have hmass : (b - s) / b + (1 / s) * (s / b) = (b - s + 1) / b := by
        field_simp
      calc
        _ = C ^ (s / b) *
            (ENNReal.ofReal A ^ ((b - s) / b) * ENNReal.ofReal A ^ (s / b)) *
            (OAI.Analysis.Fourier.Restriction.sphereMeasure n E ^ ((b - s) / b) * OAI.Analysis.Fourier.Restriction.sphereMeasure n E ^ ((1 / s) * (s / b))) := by
              simp only [mul_comm, mul_left_comm, mul_assoc]
        _ = _ := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (div_nonneg (sub_nonneg.mpr hsb) hb.le)
              (div_nonneg hs0.le hb.le), hsplit, ENNReal.rpow_one,
            ← ENNReal.rpow_add_of_nonneg _ _ (div_nonneg (sub_nonneg.mpr hsb) hb.le)
              (mul_nonneg (one_div_nonneg.mpr hs0.le) (div_nonneg hs0.le hb.le)), hmass]

end OAI.Analysis.Fourier.Restriction
