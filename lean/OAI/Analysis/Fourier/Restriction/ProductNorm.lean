import OAI.Analysis.Fourier.Restriction.AnnularIntegral
import OAI.Analysis.Fourier.BochnerRiesz.MaximalSummation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem eLpNorm_fun_fst {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {f : X → ℂ} (hf : Measurable f) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun z : X × Y ↦ f z.1) (ENNReal.ofReal p) (μ.prod ν) =
      eLpNorm f (ENNReal.ofReal p) μ * ν univ ^ (1 / p) := by
  have hm : AEStronglyMeasurable (fun z : X × Y ↦ f z.1) (μ.prod ν) :=
    (hf.comp measurable_fst).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
    hm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le, lintegral_prod _ (by fun_prop)]
  simp only [lintegral_const]
  rw [lintegral_mul_const'' _ (by fun_prop), ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]

theorem eLpNorm_radial_annulus_le {n : ℕ} (hn : 1 ≤ n)
    {f : Space n → ℂ} (hf : Measurable f) {p : ℝ} (hp : 0 < p)
    {a : ℝ} (ha : 0 < a) (b : ℝ) :
    eLpNorm (fun z : Space n × ℝ ↦ f (z.2 • z.1)) (ENNReal.ofReal p)
      ((OAI.Analysis.Fourier.Restriction.sphereMeasure n).prod (volume.restrict (Icc a b))) ≤
    ((ENNReal.ofReal (a ^ (n - 1)))⁻¹) ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hm : Measurable (fun z : Space n × ℝ ↦ f (z.2 • z.1)) := by fun_prop
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hm.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le,
    lintegral_prod _ (by fun_prop)]
  have H := lintegral_radial_annulus_le hn (hf.enorm.pow_const p) ha b
  have H' := ENNReal.rpow_le_rpow H (one_div_nonneg.mpr hp.le)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le)] using H'

end OAI.Analysis.Fourier.Restriction
