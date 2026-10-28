import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ComplexCovector
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PureOneCovector

/-! # Holomorphic Chart Pair -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicChartPair.CM.Construction

noncomputable section

/-! The genuine chartwise one-form metric on pure (1,0) covectors is the
inverse-Hermitian pairing with its required factor two. -/

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (y : V.analyticModel) (hy : y ∈ e.target)

def holomorphicMetricFiberCovector (a : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 1)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V.analyticModel 1 0 a) :
    Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy →L[ℂ] ℂ :=
  (PureOneCovector.CM.Construction.holomorphicOneCovector a ha).comp
    (Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy).toContinuousLinearMap

theorem holomorphicMetricFiberCovector_restrict (a : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 1)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V.analyticModel 1 0 a) :
    (holomorphicMetricFiberCovector V e he y hy a ha).toLinearMap.restrictScalars ℝ =
      ExteriorMetricLowDegree.CM.Construction.oneFormCovector (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy 1 a) := by
  ext u
  rfl

theorem holomorphicMetricFiberCovector_basis {ι : Type*}
    (b : Module.Basis ι ℂ V.analyticModel) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 1)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V.analyticModel 1 0 a) (i : ι) :
    (holomorphicMetricFiberCovector V e he y hy a ha).toLinearMap
      ((b.map (Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy).symm.toLinearEquiv) i) =
      a (fun _ => b i) := by
  change PureOneCovector.CM.Construction.holomorphicOneCovector a ha
    ((Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy)
      ((Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy).symm (b i))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, PureOneCovector.CM.Construction.holomorphicOneCovector_apply]

theorem projectiveChartPair_holomorphic_inverse_metric {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V.analyticModel)
    (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 1)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V.analyticModel 1 0 a) (hc : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V.analyticModel 1 0 c) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy 1 a c =
      2 * ∑ j, ∑ k, star (a (fun _ => b k)) * (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e b y)⁻¹ j k *
        c (fun _ => b j) := by
  let T := Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy
  have hG : Matrix.gram ℂ (b.map T.symm.toLinearEquiv) = InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e b y :=
    (HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_eq_gram V e he b hy).symm
  change Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair 1 (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy 1 a)
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy 1 c) = _
  rw [ExteriorMetricLowDegree.CM.Construction.formMetricPair_one, ← holomorphicMetricFiberCovector_restrict V e he y hy a ha,
    ← holomorphicMetricFiberCovector_restrict V e he y hy c hc,
    ComplexCovector.CM.Construction.covectorInner_holomorphic_inverse_gram (b.map T.symm.toLinearEquiv), hG]
  congr 1

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicChartPair.CM.Construction
