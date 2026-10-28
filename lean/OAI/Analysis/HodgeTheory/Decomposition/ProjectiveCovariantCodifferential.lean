import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovariantNumerator
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection
import OAI.Analysis.HodgeTheory.Decomposition.AdjointLocality

/-! # Projective Covariant Codifferential -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovariantCodifferential.Constructions

noncomputable section

/-! The actual global codifferential is the negative metric trace of the
genuine smooth covector connection in every projective chart. -/

open scoped ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

include he

theorem projectiveLocalAdjointCoefficients_covariant
    (a : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (n + 1))
    (ha : ContDiffOn ℝ ∞ a (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _))
    {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    AdjointCoefficients.Constructions.projectiveLocalAdjointCoefficients V e n
      (fun y => SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis (n + 1) (a y)) z =
    SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
      (CovariantAdjointPair.Constructions.bilinearCovariantCodifferential (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) a z) := by
  rw [AdjointCoefficients.Constructions.projectiveLocalAdjointCoefficients, ProjectiveCovariantNumerator.Constructions.projectiveFormalAdjointNumerator_covariant V e he n a ha hz]
  exact (AdjointCoefficients.Constructions.projectiveWeightedFormOperator_isInvertible V e he n z hz).inverse_apply_self _

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem projectiveCodifferential_covariant
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    EuclideanForms.Constructions.euclideanChartForm V e n (AdjointAlgebra.Constructions.projectiveCodifferential V n a).val z =
      -∑ i, SymbolDifferential.Constructions.exteriorContraction n
        (KoszulConnection.Constructions.bilinearMetricSharp (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
          ((stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis.coord i).toContinuousLinearMap)
        (ProjectiveCovectorConnection.Constructions.projectiveFormCovariantDerivative V e (n + 1) a z
          (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) i)) := by
  apply (SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n).injective
  change EuclideanForms.Constructions.euclideanChartCoefficients V e n (AdjointAlgebra.Constructions.projectiveCodifferential V n a).val z = _
  rw [AdjointLocality.Constructions.projectiveCodifferential_coefficients V n e he a z hz]
  exact projectiveLocalAdjointCoefficients_covariant V e he n (EuclideanForms.Constructions.euclideanChartForm V e (n + 1) a.val)
    (EuclideanForms.Constructions.euclideanChartForm_smooth V e he (n + 1) a) hz

end

end OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovariantCodifferential.Constructions
