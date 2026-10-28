import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDerivative
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric

/-! # Euclidean Metric Derivative -/

namespace OAI.Analysis.HodgeTheory.Decomposition.EuclideanMetricDerivative.Constructions

noncomputable section

/-! The genuine metric derivative in the fixed Euclidean chart model,
including the differentiated Hermitian and closedness identities. -/

open scoped ContDiff _root_.Topology

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def projectiveEuclideanMetricDerivative (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ :=
  fderiv ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) z

include he

theorem projectiveEuclideanMetric_J_skew {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u v : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z (Complex.I • u) v = -AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z u (Complex.I • v) := by
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_apply, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_apply,
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).map_smul, (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).map_smul]
  exact KahlerMetric.Constructions.projectiveMetric_J_skew V e he _ hz _ _

theorem projectiveEuclideanMetricDerivative_apply {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u v w : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    projectiveEuclideanMetricDerivative V e z u v w =
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDerivative.CM.Construction.varietyMetricDerivative V e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V u) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V v) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w) := by
  have hE := ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).contDiffAt
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hB := ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart_smooth V e he).contDiffAt
    (e.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hscalar := (hB.clm_apply (differentiableAt_const (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V v))).clm_apply
    (differentiableAt_const (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w))
  have hchain := hscalar.hasFDerivAt.comp z
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt
  have hfun : (fun y => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e y v w) =
      (fun y => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V v) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w)) ∘
        AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V := funext (fun y => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_apply V e y v w)
  change fderiv ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) z u v w = _
  rw [← AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDerivative.CM.Construction.bilinearDerivative_apply _ hE, hfun, hchain.fderiv]
  change fderiv ℝ (fun y => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V v) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w))
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V u) = _
  exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDerivative.CM.Construction.bilinearDerivative_apply _ hB _ _ _

theorem projectiveEuclideanMetricDerivative_symmetric {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u v w : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    projectiveEuclideanMetricDerivative V e z u v w = projectiveEuclideanMetricDerivative V e z u w v := by
  rw [projectiveEuclideanMetricDerivative_apply V e he hz, projectiveEuclideanMetricDerivative_apply V e he hz]
  exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDerivative.CM.Construction.varietyMetricDerivative_symmetric V e he hz _ _ _

theorem projectiveEuclideanMetricDerivative_J_skew {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u v w : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    projectiveEuclideanMetricDerivative V e z u (Complex.I • v) w =
      -projectiveEuclideanMetricDerivative V e z u v (Complex.I • w) := by
  rw [projectiveEuclideanMetricDerivative_apply V e he hz, projectiveEuclideanMetricDerivative_apply V e he hz,
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).map_smul, (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).map_smul]
  exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDerivative.CM.Construction.varietyMetricDerivative_J_skew V e he hz _ _ _

theorem projectiveEuclideanMetricDerivative_closed {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u v w : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    projectiveEuclideanMetricDerivative V e z u v (Complex.I • w) -
      projectiveEuclideanMetricDerivative V e z v u (Complex.I • w) +
      projectiveEuclideanMetricDerivative V e z w u (Complex.I • v) = 0 := by
  rw [projectiveEuclideanMetricDerivative_apply V e he hz, projectiveEuclideanMetricDerivative_apply V e he hz,
    projectiveEuclideanMetricDerivative_apply V e he hz,
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).map_smul, (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).map_smul]
  exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDerivative.CM.Construction.varietyMetricDerivative_closed V e he hz _ _ _

end

end OAI.Analysis.HodgeTheory.Decomposition.EuclideanMetricDerivative.Constructions
