import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BallMean
import OAI.AlgebraicGeometry.DivisorClass.Chern.HilbertMeanSquareBound

/-! # Ball Point Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BallPointBound

noncomputable section

/-! Actual L² control of the value at the center of a holomorphic coordinate ball. -/

open _root_.MeasureTheory Set _root_.Metric
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E]

theorem holomorphic_ball_point_bound (f : E → ℂ) {R : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball 0 R)) :
    (volume : Measure E).real (ball (0 : E) R) * ‖f 0‖ ^ 2 ≤
      ∫ x in ball (0 : E) R, ‖f x‖ ^ 2 := by
  have hfinite : (volume : Measure E) (ball (0 : E) R) < ⊤ :=
    (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : E) R).measure_lt_top
  let : Fact ((volume : Measure E) (ball (0 : E) R) < ⊤) := ⟨hfinite⟩
  have hcont : ContinuousOn f (closedBall (0 : E) R) := by
    simpa only [closure_ball (0 : E) hR.ne'] using hf.2
  have hfi : IntegrableOn f (ball (0 : E) R) :=
    (hcont.integrableOn_compact (isCompact_closedBall (0 : E) R)).mono_set ball_subset_closedBall
  have hf2 : IntegrableOn (fun x => ‖f x‖ ^ 2) (ball (0 : E) R) :=
    ((hcont.norm.pow 2).integrableOn_compact (isCompact_closedBall (0 : E) R)).mono_set ball_subset_closedBall
  have hm : (∫ x in ball (0 : E) R, f x) = (volume.restrict (ball (0 : E) R)).real Set.univ • f 0 := by
    simpa [Measure.real] using BallMean.holomorphic_ball_mean f hR hf
  simpa [Measure.real] using HilbertMeanSquareBound.hilbert_mean_square_bound (volume.restrict (ball (0 : E) R)) f (f 0) hfi hf2 hm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BallPointBound
