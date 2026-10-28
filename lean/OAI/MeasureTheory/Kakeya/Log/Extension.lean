import OAI.Analysis.Fourier.Restriction.Extension

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- Local restriction and local extension have exactly the same constant.
In particular, this duality does not turn a logarithmic loss into a power loss. -/
theorem sphericalExtension_bound_of_local_restriction {n : ℕ} {p : ℝ}
    (hp : 1 < p) {Ω : Set (Space n)} (hΩ : MeasurableSet Ω)
    (hΩfin : volume Ω ≠ ⊤) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hrestriction : ∀ f : Space n → ℂ, Measurable f → Integrable f →
      MemLp f (ENNReal.ofReal (p / (p - 1))) volume →
      (∀ x, x ∉ Ω → f x = 0) →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal (p / (p - 1))) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        C * eLpNorm f (ENNReal.ofReal (p / (p - 1))) volume)
    {g : Space n → ℂ} (hg : MemLp g (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) :
    MemLp (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal p) (volume.restrict Ω) ∧
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal p) (volume.restrict Ω) ≤
        C * eLpNorm g (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp.le
  have hgi : Integrable g (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
    memLp_one_iff_integrable.mp (hg.mono_exponent hp1)
  let u : Space n → ℂ := Ω.indicator (OAI.Analysis.Fourier.Restriction.sphericalExtension g)
  have hum : AEStronglyMeasurable u volume :=
    (OAI.Analysis.Fourier.Restriction.continuous_sphericalExtension hgi).aestronglyMeasurable.indicator hΩ
  have hut : MemLp u ⊤ volume := by
    apply memLp_top_of_bound hum (∫ ω, ‖g ω‖ ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n)
    filter_upwards [] with x
    by_cases hx : x ∈ Ω
    · simpa only [u, indicator_of_mem hx] using OAI.Analysis.Fourier.Restriction.norm_sphericalExtension_le g x
    · simpa only [u, indicator_of_notMem hx, norm_zero] using
        integral_nonneg (fun ω ↦ norm_nonneg (g ω))
  have hup : MemLp u (ENNReal.ofReal p) volume :=
    hut.mono_exponent_of_measure_support_ne_top
      (s := Ω) (fun x hx ↦ by simp [u, hx]) hΩfin le_top
  have H : eLpNorm u (ENNReal.ofReal p) volume ≤
      C * eLpNorm g (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
    apply OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_le_of_integral_mul_bound volume hp hup
    intro f hfp
    let f₀ := hfp.aestronglyMeasurable.mk f
    have heq : f =ᵐ[volume] f₀ := hfp.aestronglyMeasurable.ae_eq_mk
    have hf₀m : Measurable f₀ := hfp.aestronglyMeasurable.measurable_mk
    have hf₀p : MemLp f₀ (ENNReal.ofReal (p / (p - 1))) volume := by
      rw [MemLp, ← eLpNorm_congr_ae heq]
      exact hfp
    let v : Space n → ℂ := Ω.indicator f₀
    have hvm : Measurable v := hf₀m.indicator hΩ
    have hvp : MemLp v (ENNReal.ofReal (p / (p - 1))) volume := hf₀p.indicator hΩ
    have hvi : Integrable v := by
      apply memLp_one_iff_integrable.mp
      apply hvp.mono_exponent_of_measure_support_ne_top
        (s := Ω) (fun x hx ↦ by simp [v, hx]) hΩfin
      have hq : 1 ≤ p / (p - 1) := by
        apply (le_div_iff₀ (by linarith : 0 < p - 1)).mpr
        linarith
      exact_mod_cast ENNReal.ofReal_le_ofReal hq
    have hvs : Integrable (fun x ↦ star (v x)) :=
      memLp_one_iff_integrable.mp (memLp_one_iff_integrable.mpr hvi).star
    have hvsp : MemLp (fun x ↦ star (v x))
        (ENNReal.ofReal (p / (p - 1))) volume := hvp.star
    have hvsm : Measurable (fun x ↦ star (v x)) := by fun_prop
    have hr := hrestriction (fun x ↦ star (v x)) hvsm hvs hvsp
      (fun x hx ↦ by simp [v, hx])
    have hrm : MemLp (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ star (v x)))
        (ENNReal.ofReal (p / (p - 1))) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
      hr.trans_lt (ENNReal.mul_lt_top hC.lt_top hvsp)
    have hpair : (∫ x, f x * u x) = ∫ x, v x * OAI.Analysis.Fourier.Restriction.sphericalExtension g x := by
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      by_cases hxΩ : x ∈ Ω <;> simp [u, v, hxΩ, hx]
    rw [hpair, OAI.Analysis.Fourier.Restriction.integral_sphericalExtension_pairing hvi hgi]
    have hpq : p.HolderConjugate (p / (p - 1)) :=
      (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
    calc
      _ ≤ eLpNorm g (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) *
          eLpNorm (fun ω ↦ star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ star (v x)) ω))
            (ENNReal.ofReal (p / (p - 1))) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
        OAI.Analysis.Fourier.BochnerRiesz.enorm_integral_mul_le_eLpNorm (OAI.Analysis.Fourier.Restriction.sphereMeasure n) hg.aestronglyMeasurable
          hrm.star.aestronglyMeasurable hpq
      _ = eLpNorm g (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) *
          eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ star (v x)))
            (ENNReal.ofReal (p / (p - 1))) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
        rw [show (fun ω ↦ star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ star (v x)) ω)) =
          star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ star (v x))) from rfl, eLpNorm_star]
      _ ≤ eLpNorm g (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) *
          (C * eLpNorm (fun x ↦ star (v x))
            (ENNReal.ofReal (p / (p - 1))) volume) := mul_le_mul' le_rfl hr
      _ = (C * eLpNorm g (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) *
          eLpNorm v (ENNReal.ofReal (p / (p - 1))) volume := by
        rw [show (fun x ↦ star (v x)) = star v from rfl, eLpNorm_star]
        simp only [mul_left_comm, mul_assoc]
      _ ≤ (C * eLpNorm g (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) *
          eLpNorm f (ENNReal.ofReal (p / (p - 1))) volume := by
        apply mul_le_mul' le_rfl
        calc
          _ ≤ eLpNorm f₀ (ENNReal.ofReal (p / (p - 1))) volume :=
            eLpNorm_indicator_le _ hΩ
          _ = _ := (eLpNorm_congr_ae heq).symm
  have he : eLpNorm u (ENNReal.ofReal p) volume =
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal p) (volume.restrict Ω) :=
    eLpNorm_indicator_eq_eLpNorm_restrict hΩ
  rw [he] at H
  exact ⟨H.trans_lt (ENNReal.mul_lt_top hC.lt_top hg), H⟩

end OAI.MeasureTheory.Kakeya
