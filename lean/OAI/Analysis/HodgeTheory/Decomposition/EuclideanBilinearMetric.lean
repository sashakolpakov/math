import OAI.Analysis.HodgeTheory.Decomposition.BilinearMetricInner
import OAI.Analysis.HodgeTheory.Decomposition.EuclideanForms

/-! # Euclidean Bilinear Metric -/

namespace OAI.Analysis.HodgeTheory.Decomposition.EuclideanBilinearMetric.Constructions

noncomputable section

/-! Identification of the general alternating-covector metric with the
actual coefficient operators used to construct the projective codifferential. -/

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)

theorem euclideanBilinearGram_eq (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    BilinearFormMetric.Constructions.bilinearExteriorGram (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) =
    MetricCoefficients.Constructions.projectiveExteriorGram V e (AdjointCoefficients.Constructions.projectiveReferenceBasis V) n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) := by
  ext s t
  apply congrArg Matrix.det
  ext i j
  exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_apply V e z _ _

theorem projectiveWeightedFormOperator_eq_bilinear (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z •
      CoordinateMetric.Constructions.realMatrixOperator (BilinearFormMetric.Constructions.bilinearExteriorGram (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z))⁻¹ := by
  rw [euclideanBilinearGram_eq]
  rfl

theorem projectiveWeightedFormOperator_bilinear_pair (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (a c : DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n) :
    inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z
      (SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n a))
        (SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n c) =
      ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z : ℂ) *
        BilinearFormMetric.Constructions.bilinearFormMetricPair (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
          (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) a c).re := by
  rw [projectiveWeightedFormOperator_eq_bilinear, smul_apply, real_inner_smul_left,
    BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, CoordinateMetric.Constructions.euclidean_real_inner_eq_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

end

end OAI.Analysis.HodgeTheory.Decomposition.EuclideanBilinearMetric.Constructions
