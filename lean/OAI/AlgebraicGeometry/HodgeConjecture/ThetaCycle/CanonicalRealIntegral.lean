import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComplexRealFundamental
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntegralChartPartition
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealCoordinateMeasure

/-! # Canonical Real Integral -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CanonicalRealIntegral.CM

noncomputable section

/-! ThetaCycle: the actual canonical complex fundamental class and the real
chart integral are compared, with the fixed model simplex integer retained. -/

open _root_.CategoryTheory Set _root_.MeasureTheory
open scoped _root_.Manifold ContDiff

variable {p : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin p → ℂ) M]
  [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M]
  [IsManifold 𝓘(ℝ, Fin p → ℂ) ∞ M]

theorem recharted_cycle_integral_chart_partition
    (e : (Fin p → ℂ) ≃L[ℝ] (Fin (2 * p) → ℝ)) :
    let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
    let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
    ∀ (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition (Fin (2 * p) → ℝ) M)
      (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin (2 * p) → ℝ) M (2 * p)),
    IntegralEvaluation.CM.integralCycleEvaluation (ComplexRealFundamental.CM.rechartedIntegralCycle (M := M) e) form =
      ∑ i : D.centers, ∫ y,
        Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff (chartAt (Fin (2 * p) → ℝ) i.val) (D.partition i)
          (fun y => form.val.inChart (chartAt (Fin (2 * p) → ℝ) i.val) y
            (Pi.basisFun ℝ (Fin (2 * p)))) y := by
  let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
  let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
  dsimp only
  intro D form
  apply IntegralChartPartition.CM.integral_cycle_evaluation_chart_partition
  intro i K hK hKs
  have hs : K ⊆ (chartAt (Fin p → ℂ) i.val).source := by
    change K ⊆ ((chartAt (Fin p → ℂ) i.val).trans e.toHomeomorph.toOpenPartialHomeomorph).source at hKs
    simpa only [mfld_simps] using hKs
  exact ComplexRealFundamental.CM.recharted_integral_cycle_restrict_chart e (chartAt (Fin p → ℂ) i.val)
    (chart_mem_atlas (Fin p → ℂ) i.val) K hK hs

theorem canonical_fundamental_real_chart_integral
    (e : (Fin p → ℂ) ≃L[ℝ] (Fin (2 * p) → ℝ)) :
    let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
    let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
    ∀ (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition (Fin (2 * p) → ℝ) M)
      (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin (2 * p) → ℝ) M (2 * p)),
    ComplexRealFundamental.CM.realSimplexComplexMultiplicity p e •
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (TopCat.of M) (2 * p)
        (AlgebraicTopology.FundamentalClass.TopEvaluation.IntegrationConstruction.topIntegrationClass (2 * p) M form)
        (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ) (TopCat.of M) (2 * p)
          (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass p M)) =
      ∑ i : D.centers, ∫ y,
        Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff (chartAt (Fin (2 * p) → ℝ) i.val) (D.partition i)
          (fun y => form.val.inChart (chartAt (Fin (2 * p) → ℝ) i.val) y
            (Pi.basisFun ℝ (Fin (2 * p)))) y := by
  let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
  let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
  dsimp only
  intro D form
  have h := recharted_cycle_integral_chart_partition e D form
  change AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (TopCat.of M) (2 * p)
    (AlgebraicTopology.FundamentalClass.TopEvaluation.IntegrationConstruction.topIntegrationClass (2 * p) M form)
    (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ) (TopCat.of M) (2 * p)
      (ComplexRealFundamental.CM.realSimplexComplexMultiplicity p e • CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass p M)) = _ at h
  simpa only [map_zsmul] using h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CanonicalRealIntegral.CM
