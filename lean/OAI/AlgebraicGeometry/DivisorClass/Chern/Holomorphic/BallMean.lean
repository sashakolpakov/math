import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.CircleMean
import OAI.AlgebraicGeometry.DivisorClass.Chern.UnitRotationBallIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! # Ball Mean -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BallMean

noncomputable section

/-! The actual volume mean of a holomorphic function on a finite-dimensional complex norm ball. -/

open _root_.MeasureTheory Set _root_.Metric Real _root_.Complex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E]

theorem holomorphic_ball_mean (f : E → ℂ) {R : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball 0 R)) :
    (∫ x in ball (0 : E) R, f x) = ((volume : Measure E) (ball (0 : E) R)).toReal • f 0 := by
  have hnorm (θ : ℝ) : ‖circleMap 0 1 θ‖ = 1 := by simp [circleMap]
  have hcont : ContinuousOn (fun p : ℝ × E => f (circleMap 0 1 p.1 • p.2))
      (Icc (0 : ℝ) (2 * π) ×ˢ closedBall (0 : E) R) := by
    apply hf.2.comp (((continuous_circleMap 0 1).comp continuous_fst).smul continuous_snd).continuousOn
    intro p hp
    rw [closure_ball (0 : E) hR.ne']
    change circleMap 0 1 p.1 • p.2 ∈ closedBall (0 : E) R
    have hx := hp.2
    simpa only [mem_closedBall, dist_zero_right, norm_smul, hnorm, one_mul] using hx
  have hcompact := hcont.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall (0 : E) R))
    (μ := (volume : Measure ℝ).prod (volume : Measure E))
  have hint : Integrable (Function.uncurry (fun θ : ℝ => fun x : E => f (circleMap 0 1 θ • x)))
      ((volume.restrict (uIoc (0 : ℝ) (2 * π))).prod (volume.restrict (ball (0 : E) R))) := by
    rw [Measure.prod_restrict]
    apply hcompact.mono_set
    intro p hp
    have hθ : 0 < p.1 ∧ p.1 ≤ 2 * π := by
      simpa only [uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * π), mem_Ioc] using hp.1
    exact ⟨⟨hθ.1.le, hθ.2⟩, ball_subset_closedBall hp.2⟩
  have hswap := intervalIntegral_integral_swap hint
  calc
    _ = (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..(2 * π), (∫ x in ball (0 : E) R, f x) :=
      (circleAverage_const (∫ x in ball (0 : E) R, f x) 0 1).symm
    _ = (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..(2 * π), (∫ x in ball (0 : E) R, f (circleMap 0 1 θ • x)) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _
      exact (UnitRotationBallIntegral.unitScalarRotation_ball_integral (circleMap 0 1 θ) (hnorm θ) R f).symm
    _ = (2 * π)⁻¹ • ∫ x in ball (0 : E) R, (∫ θ in (0 : ℝ)..(2 * π), f (circleMap 0 1 θ • x)) :=
      congrArg (fun a : ℂ => (2 * π)⁻¹ • a) hswap
    _ = ∫ x in ball (0 : E) R, (2 * π)⁻¹ • (∫ θ in (0 : ℝ)..(2 * π), f (circleMap 0 1 θ • x)) :=
      (integral_smul _ _).symm
    _ = ∫ _ in ball (0 : E) R, f 0 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      exact HolomorphicLine.CircleMean.holomorphic_line_circle_mean f hf x (by simpa only [mem_ball, dist_zero_right] using hx)
    _ = _ := by simp [Measure.real]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BallMean
