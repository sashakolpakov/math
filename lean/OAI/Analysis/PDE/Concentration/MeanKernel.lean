import OAI.Analysis.PDE.Concentration.WeakLaplacian

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set Filter Metric InnerProductSpace
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def meanPotential (x : E) : ℝ := expNegInvGlue (1 - ‖x‖ ^ 2)

noncomputable def meanWeight (x : E) : ℝ := 2 * deriv expNegInvGlue (1 - ‖x‖ ^ 2)

omit [FiniteDimensional ℝ E] in
theorem contDiff_meanPotential : ContDiff ℝ ∞ (meanPotential : E → ℝ) :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

omit [FiniteDimensional ℝ E] in
theorem contDiff_meanWeight : ContDiff ℝ ∞ (meanWeight : E → ℝ) := by
  have hd : ContDiff ℝ ∞ (deriv expNegInvGlue) :=
    (contDiff_infty_iff_deriv.mp expNegInvGlue.contDiff).2
  exact contDiff_const.mul (hd.comp (contDiff_const.sub (contDiff_norm_sq ℝ)))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem meanPotential_nonneg (x : E) : 0 ≤ meanPotential x := expNegInvGlue.nonneg _

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem meanWeight_nonneg (x : E) : 0 ≤ meanWeight x :=
  mul_nonneg (by norm_num) expNegInvGlue.monotone.deriv_nonneg

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem meanPotential_zero {x : E} (hx : 1 ≤ ‖x‖) : meanPotential x = 0 := by
  apply expNegInvGlue.zero_of_nonpos
  nlinarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem meanWeight_zero {x : E} (hx : 1 < ‖x‖) : meanWeight x = 0 := by
  have hs : 1 - ‖x‖ ^ 2 < 0 := by nlinarith
  have he : expNegInvGlue =ᶠ[𝓝 (1 - ‖x‖ ^ 2)] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hs] with t ht
    exact expNegInvGlue.zero_of_nonpos (le_of_lt ht)
  simp only [meanWeight, he.deriv_eq, deriv_const, mul_zero]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem meanPotential_support : tsupport (meanPotential : E → ℝ) ⊆ closedBall 0 1 := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  simp only [mem_closedBall, dist_zero_right]
  by_contra hn
  exact hx (meanPotential_zero (le_of_lt (lt_of_not_ge hn)))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem meanWeight_support : tsupport (meanWeight : E → ℝ) ⊆ closedBall 0 1 := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  simp only [mem_closedBall, dist_zero_right]
  by_contra hn
  exact hx (meanWeight_zero (lt_of_not_ge hn))

theorem hasCompactSupport_meanPotential : HasCompactSupport (meanPotential : E → ℝ) :=
  (isCompact_closedBall 0 1).of_isClosed_subset (isClosed_tsupport _) meanPotential_support

theorem hasCompactSupport_meanWeight : HasCompactSupport (meanWeight : E → ℝ) :=
  (isCompact_closedBall 0 1).of_isClosed_subset (isClosed_tsupport _) meanWeight_support

omit [FiniteDimensional ℝ E] in
theorem fderiv_meanPotential (x y : E) :
    fderiv ℝ meanPotential x y = -meanWeight x * ⟪x, y⟫_ℝ := by
  have hs := ((show ContDiff ℝ ∞ expNegInvGlue from
    expNegInvGlue.contDiff).differentiable (by simp) (1 - ‖x‖ ^ 2)).hasDerivAt
  have hi := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_sub 1
  have h := hs.comp_hasFDerivAt x hi
  change HasFDerivAt (meanPotential : E → ℝ) _ x at h
  rw [h.fderiv]
  simp [meanWeight]
  ring

variable [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem integrable_meanWeight : Integrable (meanWeight : E → ℝ) :=
  contDiff_meanWeight.continuous.integrable_of_hasCompactSupport hasCompactSupport_meanWeight

theorem integral_meanWeight_pos [Nontrivial E] : 0 < ∫ x : E, meanWeight x := by
  have hd : deriv expNegInvGlue 1 = expNegInvGlue 1 := by
    simpa using (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) 1).deriv
  apply contDiff_meanWeight.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := (0 : E)) hasCompactSupport_meanWeight meanWeight_nonneg
  simp only [meanWeight, norm_zero, zero_pow two_ne_zero, sub_zero, hd]
  exact ne_of_gt (mul_pos (by norm_num) (expNegInvGlue.pos_of_pos (by norm_num)))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [MeasureTheory.Measure.IsAddHaarMeasure (MeasureTheory.volume : MeasureTheory.Measure E)] in
theorem meanWeight_pos {x : E} (hx : ‖x‖ < 1) : 0 < meanWeight x := by
  have ht : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  have hd (t : ℝ) : deriv expNegInvGlue t = (t⁻¹) ^ 2 * expNegInvGlue t := by
    simpa using (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) t).deriv
  rw [meanWeight, hd]
  exact mul_pos (by norm_num) (mul_pos (sq_pos_of_pos (inv_pos.mpr ht)) (expNegInvGlue.pos_of_pos ht))

omit [MeasureSpace E] [BorelSpace E] [MeasureTheory.Measure.IsAddHaarMeasure (MeasureTheory.volume : MeasureTheory.Measure E)] in
theorem meanWeight_lower_on_half_ball : ∃ c : ℝ, 0 < c ∧
    ∀ x ∈ closedBall (0 : E) (1 / 2), c ≤ meanWeight x := by
  obtain ⟨x, hx, hmin⟩ := (isCompact_closedBall (0 : E) (1 / 2)).exists_isMinOn
    ⟨0, by simp⟩ contDiff_meanWeight.continuous.continuousOn
  refine ⟨meanWeight x, meanWeight_pos ?_, hmin⟩
  have hn : ‖x‖ ≤ 1 / 2 := by simpa using hx
  linarith

end OAI.Analysis.PDE.Concentration
