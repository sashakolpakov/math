import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.VariableMetricAdjoint
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Projection
import OAI.AlgebraicGeometry.DivisorClass.Chern.CovariantDolbeaultCompatibility
import OAI.Analysis.HodgeTheory.Decomposition.AdjointManifold

/-! # Covariant Anti Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The actual metric connection pairs with antiholomorphic forms through the original Dolbeault adjoint. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.onePart_integral_pair (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    h.formIntegralPair V 1 (Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I a) b =
      h.formIntegralPair V 1 a (Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I b) := by
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair
  rw [Holomorphic.FormIntegralPair.holomorphicLineGlobalFormPair_apply, Holomorphic.FormIntegralPair.holomorphicLineGlobalFormPair_apply,
    HolomorphicMetric.Projection.holomorphicLineOnePart_point_pair V u a b ⟨x, trivial⟩]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.covariantDerivative_anti_pair
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) (b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    h.formIntegralPair V 1 b.val (h.covariantDerivative ⊤ a) =
      h.formIntegralPair V 0 (h.degreeCodifferential V 0 b.val) a := by
  calc
    _ = h.formIntegralPair V 1 (Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I b.val) (h.covariantDerivative ⊤ a) :=
      congrArg (fun c => h.formIntegralPair V 1 c (h.covariantDerivative ⊤ a))
        (Holomorphic.OneFormProjection.holomorphicLineOnePart_eq_of_anti u ⊤ b.val b.property).symm
    _ = h.formIntegralPair V 1 b.val (Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I (h.covariantDerivative ⊤ a)) :=
      h.onePart_integral_pair V b.val (h.covariantDerivative ⊤ a)
    _ = h.formIntegralPair V 1 b.val (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) :=
      congrArg (h.formIntegralPair V 1 b.val) (h.covariantDerivative_dolbeault ⊤ a)
    _ = _ := h.degreeCodifferential_pair V 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ a) b.val

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair_smulFunction_move (n : ℕ)
    (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f) :
    h.formIntegralPair V n a (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf b) =
      h.formIntegralPair V n
        (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n (fun x => star (f x)) (Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.conjugateFunction_smooth V f hf) a) b := by
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have hx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x
  rw [h.globalFormPair_inFrame V n a _ x x hx,
    h.globalFormPair_inFrame V n _ b x x hx,
    Holomorphic.SupportedForms.holomorphicLineSmoothMul_apply, Holomorphic.SupportedForms.holomorphicLineSmoothMul_apply,
    Projective.CovectorPair.projectiveTangentCovectorPair_smul_right, Projective.CovectorPair.projectiveTangentCovectorPair_smul_left,
    Complex.star_def, Complex.conj_conj]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
