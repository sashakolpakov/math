import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Integral

/-! # Translate Ball Integral -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.TranslateBallIntegral

noncomputable section

/-! Translation of an actual coordinate-ball integral to its center. -/

open _root_.MeasureTheory _root_.Metric Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem translate_ball_integral {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (x : E) (R : ℝ) (f : E → F) :
    (∫ z in ball (0 : E) R, f (x + z)) = ∫ z in ball x R, f z := by
  have hi : (fun z => (ball x R).indicator f (x + z)) =
      (ball (0 : E) R).indicator (fun z => f (x + z)) := by
    funext z
    have hz : x + z ∈ ball x R ↔ z ∈ ball (0 : E) R := by
      simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
    by_cases hm : z ∈ ball (0 : E) R
    · rw [indicator_of_mem (hz.mpr hm), indicator_of_mem hm]
    · rw [indicator_of_notMem (fun h => hm (hz.mp h)), indicator_of_notMem hm]
  calc
    _ = ∫ z, (ball (0 : E) R).indicator (fun z => f (x + z)) z := (integral_indicator measurableSet_ball).symm
    _ = ∫ z, (ball x R).indicator f (x + z) := congrArg (fun g : E → F => ∫ z, g z) hi.symm
    _ = ∫ z, (ball x R).indicator f z := integral_add_left_eq_self _ x
    _ = _ := integral_indicator measurableSet_ball

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.TranslateBallIntegral
