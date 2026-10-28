import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CovectorPair
import OAI.Analysis.HodgeTheory.Decomposition.UnitaryTypes

/-! # Unitary Forms -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.UnitaryForms

noncomputable section

/-! Unitary scalar covariance of the original projective metric on forms in every degree. -/

open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.UnitaryTypes.Constructions
attribute [local instance] NormedSpace.complexToReal

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem metricCoordinateForm_scalar_pullback
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (y : V.analyticModel) (hy : y ∈ e.target)
    (n : ℕ) (z : ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel n) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy n (Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback V.analyticModel n z a) =
      Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback (Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy) n z (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy n a) := by
  ext v
  change a (fun i => z • Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy (v i)) =
    a (fun i => Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy (z • v i))
  simp only [map_smul]

theorem projectiveChartFormPair_unitary
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (y : V.analyticModel) (hy : y ∈ e.target)
    (n : ℕ) (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) (a b : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel n) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n (Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback V.analyticModel n z a)
      (Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback V.analyticModel n z b) = Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy n a b := by
  dsimp only [Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair]
  rw [metricCoordinateForm_scalar_pullback, metricCoordinateForm_scalar_pullback]
  exact Analysis.HodgeTheory.Decomposition.UnitaryTypes.Constructions.formMetricPair_unitary n z hz _ _

theorem projectiveFormPointPair_unitary (n : ℕ) (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1)
    (a b : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) (x : V.analyticSpace) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z a) (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z b) x =
      Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a b x := by
  let e := chartAt V.analyticModel x
  have he := chart_mem_atlas V.analyticModel x
  have hx := mem_chart_source V.analyticModel x
  rw [Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair_eq_chart V e he x hx, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair_eq_chart V e he x hx,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction_inChart z a e he (e.map_source hx),
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction_inChart z b e he (e.map_source hx)]
  have hzi : ‖((z⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val]
    calc
      _ = ‖(z : ℂ)‖⁻¹ := norm_inv (z : ℂ)
      _ = 1 := by rw [hz, inv_one]
  exact projectiveChartFormPair_unitary V e he (e x) (e.map_source hx) n z⁻¹
    hzi _ _

theorem projectiveFormPointPair_action_adjoint (n : ℕ) (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1)
    (a b : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) (x : V.analyticSpace) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z a) b x =
      Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z⁻¹ b) x := by
  have h := projectiveFormPointPair_unitary V n z hz a (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z⁻¹ b) x
  rw [← Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction_mul, mul_inv_cancel, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction_one] at h
  exact h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.UnitaryForms
