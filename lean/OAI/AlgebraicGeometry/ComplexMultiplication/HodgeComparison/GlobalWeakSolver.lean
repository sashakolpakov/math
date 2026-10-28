import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalRellich
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalMetricCoefficient
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver

/-! # Global Weak Solver -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalWeakSolver.CM.Construction

noncomputable section

/-! A normalized weak scalar solver for the actual global projective
metric, from compactness and its uniformly positive coefficient. -/

open _root_.MeasureTheory InnerProductSpace

theorem variety_metric_weak_existsUnique (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (ℓ : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b →L[ℝ] ℝ)
    (hℓ : ∀ u ∈ ((GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b).restrictScalars ℝ).ker, ℓ u = 0) :
    ∃! u : (((GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b).restrictScalars ℝ).ker)ᗮ,
      ∀ v : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b,
        (∫ x, inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x
          (GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b u.val x)) (GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b v x)
          ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) = ℓ v := by
  obtain ⟨B, _, hB⟩ := GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient_bounded V C b
  obtain ⟨a, ha, hA⟩ := GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient_lower V C b
  exact CoerciveKernelSolver.CM.Construction.coefficient_graph_weak_existsUnique_orthogonal
    ((GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b).restrictScalars ℝ)
    ((GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b).restrictScalars ℝ)
    (GlobalRellich.CM.Construction.varietySobolevFunction_isCompact V C b) (GlobalSobolevGraph.CM.Construction.varietySobolevGraph_real_inner V C b)
    (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b) (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient_measurable V C b)
    (Filter.Eventually.of_forall hB) ha (Filter.Eventually.of_forall hA) ℓ hℓ

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalWeakSolver.CM.Construction
