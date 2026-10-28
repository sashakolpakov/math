import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.TensorDivergence
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.TensorIntegration

/-! # Tensor Integration -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Integration by parts for the original bundle rough Laplacian and genuine compactly supported chart tests. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveRoughLaplacian_integration (n : ℕ) (U : Opens V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) (i : V.analyticSpace)
    (c : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n)
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c)
    (hs : tsupport c ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e
    let G := Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e
    let A := h.projectiveConnectionChart V e i
    let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension
    let N := Line.RoughAnti.lineCovectorAntiDerivative n G A f
    (∫ x, (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e x : ℂ) * h.projectiveWeightChart V e i x *
      (-Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (Line.RoughAnti.lineCovectorRoughLaplacian b n B G A f x) (c x) +
        ∑ j, Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x)
          (N x (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord j).toContinuousLinearMap))
          (Line.ConnectionSymbols.lineCovectorConnectionDerivative n G A c x (b j)))) = 0 := by
  let D := ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  have hN := ((Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n)).restrictScalars ℝ).contDiff.comp_contDiffOn
    (h.projectiveCovectorConnection_smooth V e he U n a i)
  have hp := Line.TensorIntegration.lineCovectorTensorDivergence_integral_zero (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
    (h.projectiveWeightChart V e i)
    (Line.RoughAnti.lineCovectorAntiDerivative n (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension)) c D.isOpen
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).mono (fun _ hx => hx.1))
    ((h.projectiveWeightChart_smooth V e he i).mono (fun _ hx => ⟨hx.1, hx.2.2⟩)) hN hc hcompact hs
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hx.1)
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hx.1)
    (fun _ hx => Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_metric V e he hx.1)
    (fun _ hx => Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_symmetric V e he hx.1)
    (fun _ hx => h.projectiveWeightChart_derivative V e he i ⟨hx.1, hx.2.2⟩)
  simpa only [Line.RoughAnti.lineCovectorRoughLaplacian, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_neg_left, neg_neg,
    ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity] using hp

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
