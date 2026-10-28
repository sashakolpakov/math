import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Coefficient
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Neumann
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Decay

/-! Genuine whole-space solvability for small, compactly supported C^α coefficient perturbations. -/

noncomputable section
open Set Metric Laplacian
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

def coefficientFeedback {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (a : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m →L[ℝ] ℝ) α)
    (ha : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value a x = 0) :
    SupportedHolder m α R →L[ℝ] SupportedHolder m α R :=
  (supportedCoefficientAction hα.le a ha).comp (poissonHolderOperator hm hα hα1 R)

theorem norm_coefficientFeedback_le {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (a : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m →L[ℝ] ℝ) α)
    (ha : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value a x = 0) :
    ‖coefficientFeedback hm hα hα1 a ha‖ ≤ 2 * ‖a‖ * ‖poissonHolderOperator hm hα hα1 R‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖supportedCoefficientAction hα.le a ha (poissonHolderOperator hm hα hα1 R f)‖ ≤ _
  calc
    _ ≤ 2 * ‖a‖ * ‖poissonHolderOperator hm hα hα1 R f‖ :=
      norm_supportedCoefficientAction_le hα.le a ha _
    _ ≤ 2 * ‖a‖ * (‖poissonHolderOperator hm hα hα1 R‖ * ‖f‖) :=
      mul_le_mul_of_nonneg_left ((poissonHolderOperator hm hα hα1 R).le_opNorm f) (by positivity)
    _ = _ := by ring

def smallCoefficientSolutionOperator {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (a : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m →L[ℝ] ℝ) α)
    (ha : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value a x = 0)
    (hsmall : 2 * ‖a‖ * ‖poissonHolderOperator hm hα hα1 R‖ < 1) :
    SupportedHolder m α R →L[ℝ] GlobalC2Holder m α :=
  (poissonHolderOperator hm hα hα1 R).comp
    (oneSubInverse (coefficientFeedback hm hα hα1 a ha)
      ((norm_coefficientFeedback_le hm hα hα1 a ha).trans_lt hsmall))

theorem smallCoefficientSolutionOperator_solves {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (a : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m →L[ℝ] ℝ) α)
    (ha : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value a x = 0)
    (hsmall : 2 * ‖a‖ * ‖poissonHolderOperator hm hα hα1 R‖ < 1)
    (f : SupportedHolder m α R) (x : EuclideanSpace ℝ (Fin m)) :
    let u := globalC2Value (smallCoefficientSolutionOperator hm hα hα1 a ha hsmall f)
    laplacian u x - OAI.Analysis.Normed.Function.Holder.HolderMap.value a x (fderiv ℝ (fderiv ℝ u) x) = OAI.Analysis.PDE.Schauder.SupportedHolder.value f x := by
  let K := coefficientFeedback hm hα hα1 a ha
  have hK : ‖K‖ < 1 := (norm_coefficientFeedback_le hm hα hα1 a ha).trans_lt hsmall
  let g := oneSubInverse K hK f
  change laplacian (globalC2Value (poissonHolderOperator hm hα hα1 R g)) x -
    OAI.Analysis.Normed.Function.Holder.HolderMap.value a x (fderiv ℝ (fderiv ℝ (globalC2Value (poissonHolderOperator hm hα hα1 R g))) x) = _
  rw [show laplacian (globalC2Value (poissonHolderOperator hm hα hα1 R g)) x =
    OAI.Analysis.PDE.Schauder.SupportedHolder.value g x from poissonHolderOperator_solves hm hα hα1 R g x]
  rw [← supportedCoefficientAction_apply hα.le a ha]
  have he := congrArg (fun v : SupportedHolder m α R => OAI.Analysis.PDE.Schauder.SupportedHolder.value v x)
    (oneSubInverse_equation K hK f)
  exact he

theorem smallCoefficientSolutionOperator_bound {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (a : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m →L[ℝ] ℝ) α)
    (ha : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value a x = 0)
    (hsmall : 2 * ‖a‖ * ‖poissonHolderOperator hm hα hα1 R‖ < 1)
    (f : SupportedHolder m α R) :
    ‖smallCoefficientSolutionOperator hm hα hα1 a ha hsmall f‖ ≤
      ‖poissonHolderOperator hm hα hα1 R‖ *
        (‖f‖ / (1 - ‖coefficientFeedback hm hα hα1 a ha‖)) := by
  exact ((poissonHolderOperator hm hα hα1 R).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (oneSubInverse_bound _ _ f) (norm_nonneg _))

theorem smallCoefficientSolutionOperator_tendsto_zero {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (a : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m →L[ℝ] ℝ) α)
    (ha : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value a x = 0)
    (hsmall : 2 * ‖a‖ * ‖poissonHolderOperator hm hα hα1 R‖ < 1)
    (f : SupportedHolder m α R) :
    Filter.Tendsto (globalC2Value (smallCoefficientSolutionOperator hm hα hα1 a ha hsmall f))
      (Filter.cocompact _) (nhds 0) := by
  let g := oneSubInverse (coefficientFeedback hm hα hα1 a ha)
    ((norm_coefficientFeedback_le hm hα hα1 a ha).trans_lt hsmall) f
  change Filter.Tendsto (globalC2Value (poissonHolderOperator hm hα hα1 R g)) _ _
  have he : globalC2Value (poissonHolderOperator hm hα hα1 R g) =
      poissonPotential (OAI.Analysis.PDE.Schauder.SupportedHolder.value g) := funext (poissonHolderOperator_value hm hα hα1 R g)
  rw [he]
  exact poissonPotential_tendsto_zero hm _ g.continuous g.hasCompactSupport

theorem exists_small_coefficient_solution {m : ℕ} (hm : 3 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (R : ℝ) :
    ∃ ε > 0, ∀ (a : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m →L[ℝ] ℝ) α),
      (∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value a x = 0) → ‖a‖ < ε →
      ∃ T : SupportedHolder m α R →L[ℝ] GlobalC2Holder m α,
        ∀ f x, laplacian (globalC2Value (T f)) x -
          OAI.Analysis.Normed.Function.Holder.HolderMap.value a x (fderiv ℝ (fderiv ℝ (globalC2Value (T f))) x) = OAI.Analysis.PDE.Schauder.SupportedHolder.value f x := by
  let P := poissonHolderOperator hm hα hα1 R
  have hP : 0 < 2 * (‖P‖ + 1) := by positivity
  refine ⟨(2 * (‖P‖ + 1))⁻¹, inv_pos.mpr hP, ?_⟩
  intro a ha hsmall
  have ht : ‖a‖ * (2 * (‖P‖ + 1)) < 1 := by
    have h := mul_lt_mul_of_pos_right hsmall hP
    simpa only [inv_mul_cancel₀ hP.ne'] using h
  have hs : 2 * ‖a‖ * ‖P‖ < 1 := by nlinarith [norm_nonneg a]
  exact ⟨smallCoefficientSolutionOperator hm hα hα1 a ha hs,
    smallCoefficientSolutionOperator_solves hm hα hα1 a ha hs⟩

end OAI.Analysis.PDE.Schauder
