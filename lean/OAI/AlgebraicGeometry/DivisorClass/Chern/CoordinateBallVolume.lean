import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Coordinate Ball Volume -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinateBallVolume

noncomputable section

/-! The exact original coordinate-ball volume at square-root radius, including zero-dimensional coordinate spaces. -/

open _root_.MeasureTheory _root_.Metric
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem coordinateBall_volume_sqrt (d : ℕ) (hd : Module.finrank ℝ E = 2 * d) {ε : ℝ} (hε : 0 < ε) :
    (volume : Measure E).real (ball (0 : E) (Real.sqrt ε)) =
      ε ^ d * (volume : Measure E).real (ball (0 : E) 1) := by
  rw [Measure.real, Measure.addHaar_ball_of_pos volume (0 : E) (Real.sqrt_pos.mpr hε),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (Real.sqrt_nonneg ε) _), hd,
    pow_mul, Real.sq_sqrt hε.le]
  rfl

theorem coordinateBall_unit_volume_pos : 0 < (volume : Measure E).real (ball (0 : E) 1) := by
  have hp : 0 < (volume : Measure E) (ball (0 : E) 1) :=
    isOpen_ball.measure_pos volume (nonempty_ball.mpr (by norm_num))
  have ht : (volume : Measure E) (ball (0 : E) 1) < ⊤ :=
    (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : E) 1).measure_lt_top
  exact ENNReal.toReal_pos hp.ne' ht.ne

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinateBallVolume
