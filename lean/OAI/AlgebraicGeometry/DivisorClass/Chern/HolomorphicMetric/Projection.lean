import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OneFormProjection
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.FormOrthogonality
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormCompletion

/-! # Projection -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Projection

noncomputable section

/-! The actual bundle type projection is self-adjoint for the literal metric
integral and contracts the native completion norm. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal

theorem norm_le_of_inner_self_eq_inner {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (x y : F) (h : inner ℂ x x = inner ℂ x y) : ‖x‖ ≤ ‖y‖ := by
  have hc := re_inner_le_norm (𝕜 := ℂ) x y
  rw [← h, ← norm_sq_eq_re_inner] at hc
  by_cases hx : ‖x‖ = 0
  · rw [hx]
    exact norm_nonneg y
  · have hp : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    nlinarith

local instance metricProjection_realDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    FiniteDimensional ℝ V.analyticModel := FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)

theorem holomorphicLineOnePart_point_pair {U : Opens V.analyticSpace}
    (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1) (x : U) :
    HolomorphicLine.FormPair.holomorphicLineSmoothFormPair V u 1 (Holomorphic.OneFormProjection.holomorphicLineOnePart u U Complex.I a) b x =
      HolomorphicLine.FormPair.holomorphicLineSmoothFormPair V u 1 a (Holomorphic.OneFormProjection.holomorphicLineOnePart u U Complex.I b) x := by
  dsimp only [HolomorphicLine.FormPair.holomorphicLineSmoothFormPair]
  rw [Holomorphic.OneFormProjection.holomorphicLineOnePart_coordinate, Holomorphic.OneFormProjection.holomorphicLineOnePart_coordinate]
  exact congrArg (fun z : ℂ => _ * z)
    (Open.FormOrthogonality.projectiveOpenFormPair_anti_selfAdjoint V (a.val x.val) (b.val x.val) _)

theorem holomorphicLineOnePart_integral_pair (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    Holomorphic.FormIntegralPair.holomorphicLineFormIntegralPair V u 1 (Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I a) b =
      Holomorphic.FormIntegralPair.holomorphicLineFormIntegralPair V u 1 a (Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I b) := by
  unfold Holomorphic.FormIntegralPair.holomorphicLineFormIntegralPair
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  rw [Holomorphic.FormIntegralPair.holomorphicLineGlobalFormPair_apply, Holomorphic.FormIntegralPair.holomorphicLineGlobalFormPair_apply]
  exact holomorphicLineOnePart_point_pair V u a b ⟨x, trivial⟩

theorem holomorphicLineOnePart_integral_self (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    Holomorphic.FormIntegralPair.holomorphicLineFormIntegralPair V u 1 (Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I a)
      (Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I a) =
        Holomorphic.FormIntegralPair.holomorphicLineFormIntegralPair V u 1 (Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I a) a := by
  rw [← holomorphicLineOnePart_integral_pair, Holomorphic.OneFormProjection.holomorphicLineOnePart_idempotent]

theorem holomorphicLineOnePart_norm (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    ‖Holomorphic.FormCompletion.holomorphicFormL2Inclusion V u 1 (Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I a)‖ ≤
      ‖Holomorphic.FormCompletion.holomorphicFormL2Inclusion V u 1 a‖ := by
  apply norm_le_of_inner_self_eq_inner
  rw [Holomorphic.FormCompletion.holomorphicFormL2Inclusion_inner, Holomorphic.FormCompletion.holomorphicFormL2Inclusion_inner]
  exact holomorphicLineOnePart_integral_self V u a

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Projection
