import OAI.Analysis.Fourier.Restriction.Cell
import OAI.Analysis.Fourier.Restriction.Average

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal BigOperators RealInnerProductSpace
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def latticeAverage {n : ℕ} (E : Finset (Fin n → ℤ)) (f : Space n → ℂ) (ξ : Space n) : ℂ :=
  ∫ y in OAI.Analysis.Fourier.WavePackets.unitCell n, Complex.exp (-Complex.I * ((inner ℝ y ξ : ℝ) : ℂ)) *
    latticePhaseSum E (fun k ↦ f (OAI.Analysis.Fourier.WavePackets.integerVector k + y)) ξ

theorem measurable_latticeAverage_integrand {n : ℕ} (E : Finset (Fin n → ℤ))
    {f : Space n → ℂ} (hf : Measurable f) :
    Measurable (fun z : Space n × Space n ↦
      Complex.exp (-Complex.I * ((inner ℝ z.2 z.1 : ℝ) : ℂ)) *
        latticePhaseSum E (fun k ↦ f (OAI.Analysis.Fourier.WavePackets.integerVector k + z.2)) z.1) := by
  unfold latticePhaseSum
  fun_prop

theorem measurable_latticeAverage {n : ℕ} (E : Finset (Fin n → ℤ))
    {f : Space n → ℂ} (hf : Measurable f) : Measurable (latticeAverage E f) :=
  (measurable_latticeAverage_integrand E hf).stronglyMeasurable.integral_prod_right'.measurable

theorem eLpNorm_latticeAverage_le {n : ℕ} {q : ℝ} (hq : 1 ≤ q) {C : ℝ≥0∞}
    (hbound : ∀ E : Finset (Fin n → ℤ), ∀ a : (Fin n → ℤ) → ℂ,
      eLpNorm (latticePhaseSum E a) (ENNReal.ofReal q) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        C * ENNReal.ofReal ((∑ k ∈ E, ‖a k‖ ^ q) ^ (1 / q)))
    (E : Finset (Fin n → ℤ)) {f : Space n → ℂ} (hf : Measurable f) :
    eLpNorm (latticeAverage E f) (ENNReal.ofReal q) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      C * eLpNorm f (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := by linarith
  let F : Space n × Space n → ℂ := fun z ↦
    Complex.exp (-Complex.I * ((inner ℝ z.2 z.1 : ℝ) : ℂ)) *
      latticePhaseSum E (fun k ↦ f (OAI.Analysis.Fourier.WavePackets.integerVector k + z.2)) z.1
  have hFm : Measurable F := measurable_latticeAverage_integrand E hf
  have Havg := eLpNorm_average_rpow_le (OAI.Analysis.Fourier.Restriction.sphereMeasure n)
    (volume.restrict (OAI.Analysis.Fourier.WavePackets.unitCell n)) hFm hq
  have Hslice (y : Space n) :
      eLpNorm (fun ξ ↦ F (ξ, y)) (ENNReal.ofReal q) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ^ q ≤
      C ^ q * ∑ k ∈ E, ‖f (OAI.Analysis.Fourier.WavePackets.integerVector k + y)‖ₑ ^ q := by
    have he : eLpNorm (fun ξ ↦ F (ξ, y)) (ENNReal.ofReal q) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) =
        eLpNorm (latticePhaseSum E (fun k ↦ f (OAI.Analysis.Fourier.WavePackets.integerVector k + y)))
          (ENNReal.ofReal q) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
      apply eLpNorm_congr_norm_ae
        (hFm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (by
          rw [← finitePhaseSum_integerVector]
          exact (continuous_finitePhaseSum _ _).aestronglyMeasurable)
      filter_upwards [] with ξ
      simp [F, Complex.norm_exp]
    rw [he]
    have H := ENNReal.rpow_le_rpow (hbound E (fun k ↦ f (OAI.Analysis.Fourier.WavePackets.integerVector k + y))) hq0.le
    have hs0 : 0 ≤ ∑ k ∈ E, ‖f (OAI.Analysis.Fourier.WavePackets.integerVector k + y)‖ ^ q := by positivity
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le,
      ← Real.rpow_mul hs0, one_div_mul_cancel hq0.ne', Real.rpow_one] at H
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ Real.rpow_nonneg (norm_nonneg _) _)] at H
    have heq (z : ℂ) : ENNReal.ofReal (‖z‖ ^ q) = ‖z‖ₑ ^ q := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg z) hq0.le, ofReal_norm]
    simpa only [heq] using H
  have Hmass : (∫⁻ y in OAI.Analysis.Fourier.WavePackets.unitCell n,
      ∑ k ∈ E, ‖f (OAI.Analysis.Fourier.WavePackets.integerVector k + y)‖ₑ ^ q) ≤ ∫⁻ x, ‖f x‖ₑ ^ q := by
    rw [MeasureTheory.lintegral_finsetSum _ (fun k _ ↦ by fun_prop)]
    rw [OAI.Analysis.Fourier.WavePackets.lintegral_eq_tsum_unitCell (fun x ↦ ‖f x‖ₑ ^ q)]
    exact ENNReal.sum_le_tsum E
  have Hpow : eLpNorm (latticeAverage E f) (ENNReal.ofReal q) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ^ q ≤
      C ^ q * eLpNorm f (ENNReal.ofReal q) volume ^ q := by
    rw [OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hq0 hf.aestronglyMeasurable]
    calc
      _ ≤ ∫⁻ y in OAI.Analysis.Fourier.WavePackets.unitCell n,
          eLpNorm (fun ξ ↦ F (ξ, y)) (ENNReal.ofReal q) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ^ q := Havg
      _ ≤ ∫⁻ y in OAI.Analysis.Fourier.WavePackets.unitCell n, C ^ q *
          ∑ k ∈ E, ‖f (OAI.Analysis.Fourier.WavePackets.integerVector k + y)‖ₑ ^ q := lintegral_mono Hslice
      _ = C ^ q * ∫⁻ y in OAI.Analysis.Fourier.WavePackets.unitCell n,
          ∑ k ∈ E, ‖f (OAI.Analysis.Fourier.WavePackets.integerVector k + y)‖ₑ ^ q := by
        apply lintegral_const_mul''
        fun_prop
      _ ≤ _ := mul_le_mul le_rfl Hmass zero_le zero_le
  have H := ENNReal.rpow_le_rpow Hpow (one_div_nonneg.mpr hq0.le)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hq0.le),
    ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one] using H

end OAI.Analysis.Fourier.Restriction
