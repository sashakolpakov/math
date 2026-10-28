import OAI.RepresentationTheory.Weil.UnitarySplitting.FieldModulus
import OAI.RepresentationTheory.Weil.UnitarySplitting.TestSpaceAnalysis

/-! # Modulus Measure -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.ModulusMeasure.Construction

noncomputable section

/-! A ball-volume formula and measurability for the additive Haar modulus. -/

open _root_.MeasureTheory _root_.Metric
open scoped NNReal ENNReal

variable {F : Type} [NormedField F] [LocallyCompactSpace F]
variable [MeasurableSpace F] [BorelSpace F]
variable (hF : ¬ DiscreteTopology F)

include hF in
theorem fieldModulus_ball (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] (a : Fˣ) :
    (FieldModulus.Construction.fieldModulus F a : ℝ) = (μ (ball 0 ‖(a : F)‖)).toReal / (μ (ball 0 1)).toReal := by
  let : ProperSpace F := TestSpaceAnalysis.Construction.localField_proper F hF
  have hpos : 0 < (μ (ball (0 : F) 1)).toReal :=
    ENNReal.toReal_pos (isOpen_ball.measure_pos μ (nonempty_ball.mpr zero_lt_one)).ne'
      ((measure_mono ball_subset_closedBall).trans_lt
        (isCompact_closedBall (0 : F) 1).measure_lt_top).ne
  have hp : (FieldModulus.Construction.fieldDilation a) ⁻¹' ball (0 : F) ‖(a : F)‖ = ball 0 1 := by
    ext x
    change dist ((a : F) * x) 0 < ‖(a : F)‖ ↔ dist x 0 < 1
    rw [dist_zero_right, dist_zero_right, norm_mul]
    simpa only [mul_one] using
      (mul_lt_mul_iff_right₀ (norm_pos_iff.mpr a.ne_zero) :
        ‖(a : F)‖ * ‖x‖ < ‖(a : F)‖ * 1 ↔ ‖x‖ < 1)
  have hh := addEquivAddHaarChar_smul_preimage μ (FieldModulus.Construction.fieldDilation a)
    (X := ball (0 : F) ‖(a : F)‖)
  rw [hp] at hh
  have hr := congrArg ENNReal.toReal hh
  change ((FieldModulus.Construction.fieldModulus F a : ℝ≥0∞) * μ (ball (0 : F) 1)).toReal =
    (μ (ball 0 ‖(a : F)‖)).toReal at hr
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal] at hr
  exact (eq_div_iff hpos.ne').mpr hr

include hF in
theorem fieldModulus_measurable [MeasurableSpace Fˣ] [BorelSpace Fˣ] :
    Measurable (FieldModulus.Construction.fieldModulus F) := by
  apply measurable_coe_nnreal_real_iff.mp
  let μ : Measure F := Measure.addHaar
  have hm : Monotone (fun r : ℝ => μ (ball (0 : F) r)) :=
    fun r s hrs => measure_mono (ball_subset_ball hrs)
  have heq : (fun a : Fˣ => (FieldModulus.Construction.fieldModulus F a : ℝ)) =
      fun a : Fˣ => (μ (ball 0 ‖(a : F)‖)).toReal / (μ (ball 0 1)).toReal :=
    funext (fieldModulus_ball hF μ)
  rw [heq]
  exact (ENNReal.measurable_toReal.comp
    (hm.measurable.comp Units.continuous_val.norm.measurable)).div_const _

include hF in
theorem fieldModulus_mono_norm (a b : Fˣ) (hab : ‖(a : F)‖ ≤ ‖(b : F)‖) :
    FieldModulus.Construction.fieldModulus F a ≤ FieldModulus.Construction.fieldModulus F b := by
  let : ProperSpace F := TestSpaceAnalysis.Construction.localField_proper F hF
  let μ : Measure F := Measure.addHaar
  have hfin : μ (ball 0 ‖(b : F)‖) ≠ ∞ :=
    ((measure_mono ball_subset_closedBall).trans_lt
      (isCompact_closedBall (0 : F) ‖(b : F)‖).measure_lt_top).ne
  have hnum := ENNReal.toReal_mono hfin (measure_mono (ball_subset_ball hab))
  change (FieldModulus.Construction.fieldModulus F a : ℝ) ≤ (FieldModulus.Construction.fieldModulus F b : ℝ)
  rw [fieldModulus_ball hF μ a, fieldModulus_ball hF μ b]
  exact div_le_div_of_nonneg_right hnum ENNReal.toReal_nonneg

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.ModulusMeasure.Construction
