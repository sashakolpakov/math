import OAI.Analysis.Fourier.Cone.Slicing
import OAI.Analysis.Fourier.SquareFunction.DilationNorm
import OAI.Analysis.Fourier.Restriction.Markov

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Cone

/-- Finite-power Fubini for actual Lp functions. -/
theorem cone_ae_memLp_slice {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {F : X × Y → ℂ} (hF : Measurable F) {p : ℝ} (hp : 0 < p)
    (hf : MemLp F (ENNReal.ofReal p) (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => F (x, y)) (ENNReal.ofReal p) ν := by
  have hpow := hF.enorm.pow_const p
  have hfin := ae_lt_top hpow.lintegral_prod_right'
    (show (∫⁻ x, ∫⁻ y, ‖F (x, y)‖ₑ ^ p ∂ν ∂μ) ≠ ⊤ by
      rw [← lintegral_prod _ hpow.aemeasurable]
      have H := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by positivity)
        ENNReal.ofReal_ne_top hf
      rw [ENNReal.toReal_ofReal hp.le] at H
      exact H.ne)
  filter_upwards [hfin] with x hx
  have hm : AEStronglyMeasurable (fun y => F (x,y)) ν :=
    (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by positivity)
    ENNReal.ofReal_ne_top hm).mpr
  simpa only [ENNReal.toReal_ofReal hp.le] using hx

/-- Fiberwise Lp bounds integrate to the same bound over product spaces. -/
theorem cone_product_norm_bound {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (τ : Measure Z)
    [SFinite μ] [SFinite ν] [SFinite τ]
    {F : X × Y → ℂ} {G : X × Z → ℂ} (hF : Measurable F) (hG : Measurable G)
    {p : ℝ} (hp : 0 < p) {C : ℝ≥0∞}
    (hb : ∀ᵐ x ∂μ, eLpNorm (fun z => G (x,z)) (ENNReal.ofReal p) τ ≤
      C * eLpNorm (fun y => F (x,y)) (ENNReal.ofReal p) ν) :
    eLpNorm G (ENNReal.ofReal p) (μ.prod τ) ≤ C * eLpNorm F (ENNReal.ofReal p) (μ.prod ν) := by
  have hpow : (∫⁻ z, ‖G z‖ₑ ^ p ∂μ.prod τ) ≤ C ^ p * (∫⁻ z, ‖F z‖ₑ ^ p ∂μ.prod ν) := by
    rw [lintegral_prod _ (hG.enorm.pow_const p).aemeasurable,
      lintegral_prod _ (hF.enorm.pow_const p).aemeasurable,
      ← lintegral_const_mul _ (hF.enorm.pow_const p).lintegral_prod_right']
    apply lintegral_mono_ae
    filter_upwards [hb] with x hx
    have HH := ENNReal.rpow_le_rpow hx hp.le
    have hGx : AEStronglyMeasurable (fun z => G (x,z)) τ :=
      (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    have hFx : AEStronglyMeasurable (fun y => F (x,y)) ν :=
      (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le,
      OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp hGx,
      OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp hFx] at HH
    exact HH
  have H := ENNReal.rpow_le_rpow hpow (one_div_nonneg.mpr hp.le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one] at H
  simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity : ENNReal.ofReal p ≠ 0)
      ENNReal.ofReal_ne_top hG.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity : ENNReal.ofReal p ≠ 0)
      ENNReal.ofReal_ne_top hF.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le, one_div] using H

def coneSpatialSlices {n : ℕ} (F : ℝ × Space n → ℂ) (p : ℝ × Space n) : ℂ :=
  OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω => F (p.1,ω)) (p.1 • p.2)

theorem measurable_coneSpatialSlices {n : ℕ} {F : ℝ × Space n → ℂ}
    (hF : Measurable F) : Measurable (coneSpatialSlices F) := by
  have hm : StronglyMeasurable (fun z : (ℝ × Space n) × Space n =>
      Complex.exp (Complex.I * ((inner ℝ (z.1.1 • z.1.2) z.2 : ℝ) : ℂ)) * F (z.1.1,z.2)) := by
    apply Measurable.stronglyMeasurable
    have hFc : Measurable (fun z : (ℝ × Space n) × Space n => F (z.1.1,z.2)) :=
      hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    fun_prop
  exact (hm.integral_prod_right' (ν := OAI.Analysis.Fourier.Restriction.sphereMeasure n)).measurable

theorem coneSpatialSlices_bound {n : ℕ} {p : ℝ} (hp : 1 ≤ p) {C : ℝ≥0∞}
    (hsphere : ∀ f : Space n → ℂ, MemLp f (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension f) (ENNReal.ofReal p) volume ≤
        C * eLpNorm f (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    {F : ℝ × Space n → ℂ} (hF : Measurable F)
    (hf : MemLp F (ENNReal.ofReal p) (coneRadialMeasure.prod (OAI.Analysis.Fourier.Restriction.sphereMeasure n))) :
    eLpNorm (coneSpatialSlices F) (ENNReal.ofReal p) (coneRadialMeasure.prod volume) ≤
      C * eLpNorm F (ENNReal.ofReal p) (coneRadialMeasure.prod (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) := by
  have hp0 : 0 < p := by linarith
  apply cone_product_norm_bound coneRadialMeasure (OAI.Analysis.Fourier.Restriction.sphereMeasure n) volume hF
    (measurable_coneSpatialSlices hF) hp0
  filter_upwards [cone_ae_memLp_slice _ _ hF hp0 hf, ae_restrict_mem measurableSet_Icc]
    with ρ hρ hρI
  change eLpNorm (fun x => OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω => F (ρ,ω)) (ρ • x)) _ _ ≤ _
  rw [OAI.Analysis.Fourier.SquareFunction.eLpNorm_dilate_any _ _ (show 0 < ρ by linarith [hρI.1])]
  have hc : ENNReal.ofReal ((ρ ^ n)⁻¹) ^ (1 / (ENNReal.ofReal p).toReal) ≤ 1 := by
    apply ENNReal.rpow_le_one _ (by positivity)
    apply ENNReal.ofReal_le_one.mpr
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hρI.1)
  calc
    _ ≤ 1 * eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω => F (ρ,ω))) (ENNReal.ofReal p) volume :=
      mul_le_mul' hc le_rfl
    _ ≤ _ := by simpa only [one_mul] using hsphere _ hρ

end OAI.Analysis.Fourier.Cone
