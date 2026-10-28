import OAI.Analysis.HodgeTheory.Decomposition.KahlerCommutator
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovariantCodifferential

/-! # Projective Kahler Commutator -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ProjectiveKahlerCommutator.Constructions

noncomputable section

/-! The full Kähler commutator for the actual projective metric, genuine
smooth chart forms, and the constructed global codifferential. -/

open scoped ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem projectiveConnectionCoefficient_twisted_symmetric {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u v : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e z (Complex.I • u) v =
      ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e z (Complex.I • v) u := by
  rw [ProjectiveConnection.Constructions.projectiveConnectionCoefficient_J_left V e he hz,
    ProjectiveConnection.Constructions.projectiveConnectionCoefficient_J_left V e he hz,
    ProjectiveConnection.Constructions.projectiveConnectionCoefficient_symmetric V e he hz u v]

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem projectiveKahlerCommutator_zero
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    LefschetzSymbol.Constructions.metricLefschetzContraction 0 (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
      (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
      (CovectorSymbolAction.Constructions.twistedExteriorDerivative 1 (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
        (EuclideanForms.Constructions.euclideanChartForm V e 1 a.val) z) =
      EuclideanForms.Constructions.euclideanChartForm V e 0 (AdjointAlgebra.Constructions.projectiveCodifferential V 0 a).val z := by
  have h := KahlerCommutator.Constructions.kahlerCommutator_zero (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (EuclideanForms.Constructions.euclideanChartForm V e 1 a.val) z
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz)
    (EuclideanMetricDerivative.Constructions.projectiveEuclideanMetric_J_skew V e he hz) (projectiveConnectionCoefficient_twisted_symmetric V e he hz)
  have hd := ProjectiveCovariantCodifferential.Constructions.projectiveCodifferential_covariant V e he 0 a hz
  exact h.trans hd.symm

theorem projectiveKahlerCommutator (n : ℕ)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1 + 1))
    {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    LefschetzSymbol.Constructions.metricLefschetzContraction (n + 1) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
        (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
        (CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1) (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
          (EuclideanForms.Constructions.euclideanChartForm V e (n + 1 + 1) a.val) z) -
      CovectorSymbolAction.Constructions.twistedExteriorDerivative n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
        (fun y => LefschetzSymbol.Constructions.metricLefschetzContraction n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e y)
          (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
          (EuclideanForms.Constructions.euclideanChartForm V e (n + 1 + 1) a.val y)) z =
      EuclideanForms.Constructions.euclideanChartForm V e (n + 1) (AdjointAlgebra.Constructions.projectiveCodifferential V (n + 1) a).val z := by
  have h := KahlerCommutator.Constructions.kahlerCommutator (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
    (EuclideanForms.Constructions.euclideanChartForm V e (n + 1 + 1) a.val) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he) (fun _ hy => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hy) hz
    (EuclideanForms.Constructions.euclideanChartForm_smooth V e he (n + 1 + 1) a)
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz) (EuclideanMetricDerivative.Constructions.projectiveEuclideanMetric_J_skew V e he hz)
    (ProjectiveConnection.Constructions.projectiveConnectionCoefficient_metric V e he hz) (ProjectiveConnection.Constructions.projectiveConnectionCoefficient_J_right V e he hz)
    (projectiveConnectionCoefficient_twisted_symmetric V e he hz)
  have hd := ProjectiveCovariantCodifferential.Constructions.projectiveCodifferential_covariant V e he (n + 1) a hz
  exact h.trans hd.symm

end

end OAI.Analysis.HodgeTheory.Decomposition.ProjectiveKahlerCommutator.Constructions
