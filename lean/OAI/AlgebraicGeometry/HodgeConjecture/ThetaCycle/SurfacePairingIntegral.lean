import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfaceWedgeCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CanonicalRealIntegral

/-! # Surface Pairing Integral -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfacePairingIntegral.CM

noncomputable section

/-! ThetaCycle: the previously constructed surface pairing is the actual
fundamental-class integral of the native exterior product, up to the
explicit model simplex integer and the real-coordinate ordering sign. -/

open _root_.CategoryTheory Set _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open scoped _root_.Manifold ContDiff

variable {M : Type} [TopologicalSpace M] [ChartedSpace HeckeCycles.GeometricSource.CM.BallChart M]
  [IsManifold 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) ∞ M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
theorem surface_wedge_real_integral_eq_pairing
    (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition HeckeCycles.GeometricSource.CM.BallChart M) (α β : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart M 2)
    (hα : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 α.val)
    (hβ : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 β.val) :
    let e := Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv 2
    let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
    let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
    (∑ i : D.centers, ∫ y,
      Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff ((chartAt HeckeCycles.GeometricSource.CM.BallChart i.val).trans e.toHomeomorph.toOpenPartialHomeomorph)
        (D.partition i)
        (fun y => (RealModelForms.CM.linearRechartForms e 4 (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm β))).val.inChart
          ((chartAt HeckeCycles.GeometricSource.CM.BallChart i.val).trans e.toHomeomorph.toOpenPartialHomeomorph)
          y (Pi.basisFun ℝ (Fin 4))) y) =
      -Analysis.HodgeTheory.TopForms.Constructions.PolarizedPairing.topPairingWith D (Pi.basisFun ℂ (Fin 2)) α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm β) := by
  let e := Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv 2
  let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
  let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
  dsimp only
  rw [Analysis.HodgeTheory.TopForms.Constructions.PolarizedPairing.topPairingWith, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← RealCoordinateMeasure.CM.integral_complex_real_coordinates 2, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with z
  simpa only [Analysis.HodgeTheory.TopForms.Constructions.PolarizedPairing.topPairingIntegrand, Function.comp_apply] using!
    SurfaceWedgeCoordinates.CM.surface_wedge_real_chart_cutoff α β hα hβ (chartAt HeckeCycles.GeometricSource.CM.BallChart i.val)
      (chart_mem_atlas HeckeCycles.GeometricSource.CM.BallChart i.val) (D.partition i) z

variable [IsManifold 𝓘(ℂ, HeckeCycles.GeometricSource.CM.BallChart) 1 M]

theorem canonical_surface_wedge_pairing
    (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition HeckeCycles.GeometricSource.CM.BallChart M) (α β : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart M 2)
    (hα : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 α.val)
    (hβ : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 β.val) :
    let e := Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv 2
    let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
    let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
    ComplexRealFundamental.CM.realSimplexComplexMultiplicity 2 e •
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (TopCat.of M) 4
        (AlgebraicTopology.FundamentalClass.TopEvaluation.IntegrationConstruction.topIntegrationClass 4 M
          (RealModelForms.CM.linearRechartForms e 4 (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm β))))
        (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ) (TopCat.of M) 4
          (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass 2 M)) =
      -Analysis.HodgeTheory.TopForms.Constructions.PolarizedPairing.topPairingWith D (Pi.basisFun ℂ (Fin 2)) α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm β) := by
  let e := Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv 2
  let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
  let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
  have h := CanonicalRealIntegral.CM.canonical_fundamental_real_chart_integral e (RechartPartition.CM.linearRechartPartition e D)
    (RealModelForms.CM.linearRechartForms e 4 (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm β)))
  exact h.trans (surface_wedge_real_integral_eq_pairing D α β hα hβ)

theorem canonical_surface_wedge_nonzero (α β : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart M 2)
    (hα : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 α.val)
    (hβ : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 β.val)
    (hne : SurfacePairing.CM.surfaceConjugatePairing α β ≠ 0) :
    let e := Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv 2
    let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
    let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (TopCat.of M) 4
      (AlgebraicTopology.FundamentalClass.TopEvaluation.IntegrationConstruction.topIntegrationClass 4 M
        (RealModelForms.CM.linearRechartForms e 4 (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm β))))
      (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ) (TopCat.of M) 4
        (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass 2 M)) ≠ 0 := by
  let e := Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv 2
  let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
  let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
  have h := canonical_surface_wedge_pairing (Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.canonicalChartPartition HeckeCycles.GeometricSource.CM.BallChart M) α β hα hβ
  dsimp only
  intro hz
  dsimp only at h
  rw [hz, smul_zero] at h
  exact hne (neg_eq_zero.mp h.symm)

theorem canonical_surface_self_wedge_nonzero (α : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart M 2)
    (hα : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 α.val) (hne : α ≠ 0) :
    let e := Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv 2
    let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
    let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (TopCat.of M) 4
      (AlgebraicTopology.FundamentalClass.TopEvaluation.IntegrationConstruction.topIntegrationClass 4 M
        (RealModelForms.CM.linearRechartForms e 4 (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm α))))
      (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ) (TopCat.of M) 4
        (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass 2 M)) ≠ 0 :=
  canonical_surface_wedge_nonzero α α hα hα (SurfacePairing.CM.surface_conjugate_pairing_positive α hα hne).2.2

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfacePairingIntegral.CM
