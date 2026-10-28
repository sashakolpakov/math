import OAI.Analysis.HodgeTheory.Decomposition.CovectorMetricDifferential
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection

/-! # Projective Metric Compatibility -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ProjectiveMetricCompatibility.Constructions

noncomputable section

/-! Metric compatibility for genuine projective forms, with the explicit
Euclidean pairing identified with the actual global pointwise metric. -/

open scoped ContDiff _root_.Topology

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

include he

theorem projectivePointPair_eq_bilinearFormMetricPair
    (a c : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a c (MeasureVolume.Constructions.chartCoordinateInverse V e z) =
      BilinearFormMetric.Constructions.bilinearFormMetricPair (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (EuclideanForms.Constructions.euclideanChartForm V e n a z) (EuclideanForms.Constructions.euclideanChartForm V e n c z) := by
  let L : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V ≃L[ℝ] V.analyticModel :=
    { toLinearEquiv := (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toLinearEquiv.restrictScalars ℝ
      continuous_toFun := (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).continuous
      continuous_invFun := (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.continuous }
  have ht := BilinearMetricTransport.Constructions.bilinearFormMetricPair_transport (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    (AdjointCoefficients.Constructions.projectiveReferenceBasis V) n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz)
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart_symmetric V e he hz) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart_positive V e he hz)
    L (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_apply V e z) (a.inChart e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))
      (c.inChart e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))
  have hc := MetricCoefficients.Constructions.projectiveChartFormPair_coordinate_formula V e he (AdjointCoefficients.Constructions.projectiveReferenceBasis V) n
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz (a.inChart e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))
      (c.inChart e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))
  have hp := ProjectiveFormMetric.Constructions.projectiveFormPointPair_eq_chart V e he (e.symm (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) (e.map_target hz) n a c
  simp only [e.right_inv hz] at hp
  exact hp.trans (hc.trans ht.symm)

theorem projectiveFormPointPair_covariant_derivative
    (a c : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    fderiv ℝ (fun y => ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val c.val (MeasureVolume.Constructions.chartCoordinateInverse V e y)) z u =
      BilinearFormMetric.Constructions.bilinearFormMetricPair (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (EuclideanForms.Constructions.euclideanChartForm V e n a.val z) (ProjectiveCovectorConnection.Constructions.projectiveFormCovariantDerivative V e n c z u) +
      BilinearFormMetric.Constructions.bilinearFormMetricPair (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (ProjectiveCovectorConnection.Constructions.projectiveFormCovariantDerivative V e n a z u) (EuclideanForms.Constructions.euclideanChartForm V e n c.val z) := by
  have heq : (fun y => ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val c.val (MeasureVolume.Constructions.chartCoordinateInverse V e y)) =ᶠ[𝓝 z]
      (fun y => BilinearFormMetric.Constructions.bilinearFormMetricPair (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e y) (EuclideanForms.Constructions.euclideanChartForm V e n a.val y) (EuclideanForms.Constructions.euclideanChartForm V e n c.val y)) := by
    filter_upwards [(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with y hy
    exact projectivePointPair_eq_bilinearFormMetricPair V e he n a.val c.val hy
  rw [heq.fderiv_eq]
  apply CovectorMetricDifferential.Constructions.bilinearFormMetricPair_covariant_derivative
  · exact ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).contDiffAt
      ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  · exact ((EuclideanForms.Constructions.euclideanChartForm_smooth V e he n a).contDiffAt
      ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  · exact ((EuclideanForms.Constructions.euclideanChartForm_smooth V e he n c).contDiffAt
      ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  · exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz
  · exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz
  · exact ProjectiveConnection.Constructions.projectiveConnectionCoefficient_metric V e he hz u

end

end OAI.Analysis.HodgeTheory.Decomposition.ProjectiveMetricCompatibility.Constructions
