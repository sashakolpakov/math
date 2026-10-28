import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicChartPair
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ComplexCovector

/-! # Holomorphic Mixed Chart Pair -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicMixedChartPair.CM.Construction

noncomputable section

/-! Pairing a pure (1,0) form against an arbitrary one-form uses precisely
the latter's holomorphic covector coefficients. -/

def oneCovectorCLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) : E →L[ℝ] ℂ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)).symm a

theorem oneCovectorCLM_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (u : E) : oneCovectorCLM a u = a (fun _ => u) := rfl

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (y : V.analyticModel) (hy : y ∈ e.target)

theorem metricCoordinateForm_oneCovector (a : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 1) :
    oneCovectorCLM (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy 1 a) =
      (oneCovectorCLM a).comp
        ((Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy).toContinuousLinearMap.restrictScalars ℝ) := by
  ext u
  rfl

theorem projectiveChartPair_holomorphic_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V.analyticModel) (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 1)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V.analyticModel 1 0 a) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy 1 a c =
      2 * ∑ j, ∑ k, star (a (fun _ => b k)) * (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e b y)⁻¹ j k *
        ComplexCovector.CM.Construction.holomorphicCovectorProjection (oneCovectorCLM c) (b j) := by
  let T := Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy
  let f := HolomorphicChartPair.CM.Construction.holomorphicMetricFiberCovector V e he y hy a ha
  let g := oneCovectorCLM (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy 1 c)
  have hG : Matrix.gram ℂ (b.map T.symm.toLinearEquiv) = InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e b y :=
    (HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_eq_gram V e he b hy).symm
  have hg : ComplexCovector.CM.Construction.holomorphicCovectorProjection g =
      (ComplexCovector.CM.Construction.holomorphicCovectorProjection (oneCovectorCLM c)).comp T.toContinuousLinearMap := by
    rw [show g = (oneCovectorCLM c).comp (T.toContinuousLinearMap.restrictScalars ℝ) from
      metricCoordinateForm_oneCovector V e he y hy c]
    exact ComplexCovector.CM.Construction.holomorphicCovectorProjection_comp _ _
  change Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair 1 (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy 1 a)
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy 1 c) = _
  rw [ExteriorMetricLowDegree.CM.Construction.formMetricPair_one, ← HolomorphicChartPair.CM.Construction.holomorphicMetricFiberCovector_restrict V e he y hy a ha]
  change Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner (f.toLinearMap.restrictScalars ℝ) g.toLinearMap = _
  rw [ComplexCovector.CM.Construction.covectorInner_holomorphic_projection
    (stdOrthonormalBasis ℂ (Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy)),
    ComplexCovector.CM.Construction.covectorInner_holomorphic_inverse_gram (b.map T.symm.toLinearEquiv), hG, hg]
  congr 1

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicMixedChartPair.CM.Construction
