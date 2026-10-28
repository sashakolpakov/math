import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Unit Rotation Ball Integral -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.UnitRotationBallIntegral

noncomputable section

section

/-! Multiplication by an actual unit-norm complex scalar is a real linear isometry of the original coordinate space. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def unitScalarRotation (c : ℂ) (hc : ‖c‖ = 1) : E ≃ₗᵢ[ℝ] E where
  toFun x := c • x
  invFun x := c⁻¹ • x
  left_inv x := by
    have hne : c ≠ 0 := norm_ne_zero_iff.mp (hc.trans_ne one_ne_zero)
    change c⁻¹ • (c • x) = x
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  right_inv x := by
    have hne : c ≠ 0 := norm_ne_zero_iff.mp (hc.trans_ne one_ne_zero)
    change c • (c⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
  map_add' x y := smul_add c x y
  map_smul' r x := smul_comm c r x
  norm_map' x := by
    change ‖c • x‖ = ‖x‖
    rw [norm_smul, hc, one_mul]

theorem unitScalarRotation_apply (c : ℂ) (hc : ‖c‖ = 1) (x : E) : unitScalarRotation E c hc x = c • x := rfl

end

/-! The original volume integral over a norm ball is invariant under actual unit-scalar rotations. -/

open _root_.MeasureTheory Set _root_.Metric
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E]

theorem unitScalarRotation_ball_integral (c : ℂ) (hc : ‖c‖ = 1) (R : ℝ) (f : E → ℂ) :
    (∫ x in ball (0 : E) R, f (c • x)) = ∫ x in ball (0 : E) R, f x := by
  classical
  let T := unitScalarRotation E c hc
  have hmem (x : E) : T x ∈ ball (0 : E) R ↔ x ∈ ball (0 : E) R := by
    simp only [mem_ball, dist_zero_right, T.norm_map]
  have heq : (fun x => (ball (0 : E) R).indicator f (T x)) =
      (ball (0 : E) R).indicator (fun x => f (c • x)) := by
    funext x
    by_cases hx : x ∈ ball (0 : E) R
    · rw [indicator_of_mem ((hmem x).mpr hx), indicator_of_mem hx]
      rfl
    · rw [indicator_of_notMem ((hmem x).not.mpr hx), indicator_of_notMem hx]
  have hi := MeasureTheory.integral_comp T ((ball (0 : E) R).indicator f)
  simpa only [heq, integral_indicator measurableSet_ball] using hi

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.UnitRotationBallIntegral
