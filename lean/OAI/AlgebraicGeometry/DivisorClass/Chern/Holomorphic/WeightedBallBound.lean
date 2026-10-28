import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BallPointBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedPointWeight

/-! # Weighted Ball Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.WeightedBallBound

noncomputable section

/-! The original holomorphic ball point estimate with the actual reciprocal-power integral. -/

open _root_.MeasureTheory _root_.Metric Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E]

theorem holomorphic_weighted_ball_bound (f : E → ℂ) (m : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hf : DiffContOnCl ℂ f (ball 0 (Real.sqrt ε))) :
    (volume : Measure E).real (ball (0 : E) (Real.sqrt ε)) * ‖f 0‖ ^ 2 ≤
      (2 * ε) ^ m * ∫ z in ball (0 : E) (Real.sqrt ε), RegularizedPointWeight.regularizedPointWeight m ε z * ‖f z‖ ^ 2 := by
  have hR : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hcont : ContinuousOn f (closedBall (0 : E) (Real.sqrt ε)) := by
    simpa only [closure_ball (0 : E) hR.ne'] using hf.2
  have hi : IntegrableOn (fun z => ‖f z‖ ^ 2) (ball (0 : E) (Real.sqrt ε)) :=
    ((hcont.norm.pow 2).integrableOn_compact (isCompact_closedBall (0 : E) _)).mono_set ball_subset_closedBall
  have hw : IntegrableOn (fun z => RegularizedPointWeight.regularizedPointWeight m ε z * ‖f z‖ ^ 2)
      (ball (0 : E) (Real.sqrt ε)) :=
    (((RegularizedPointWeight.regularizedPointWeight_continuous m hε).continuousOn.mul (hcont.norm.pow 2)).integrableOn_compact
      (isCompact_closedBall (0 : E) _)).mono_set ball_subset_closedBall
  calc
    _ ≤ ∫ z in ball (0 : E) (Real.sqrt ε), ‖f z‖ ^ 2 := BallPointBound.holomorphic_ball_point_bound f hR hf
    _ ≤ ∫ z in ball (0 : E) (Real.sqrt ε),
        (2 * ε) ^ m * (RegularizedPointWeight.regularizedPointWeight m ε z * ‖f z‖ ^ 2) := by
      apply integral_mono_ae hi (hw.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      exact RegularizedPointWeight.regularizedPointWeight_ball_bound m hε hz (‖f z‖ ^ 2) (sq_nonneg _)
    _ = _ := integral_const_mul _ _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.WeightedBallBound
