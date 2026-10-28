import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.MetricCoordinates
import OAI.Analysis.HodgeTheory.Decomposition.EuclideanBilinearMetric

/-! # Metric Operator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The genuine positive line-weighted metric matrices in the original projective form coordinates. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.EuclideanBilinearMetric.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightChart_real (i : V.analyticSpace) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    ((h.projectiveWeightChart V e i z).re : ℂ) = h.projectiveWeightChart V e i z := by
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightChart Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension
  split_ifs <;> rfl

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedFormOperator (i : V.analyticSpace) (n : ℕ) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n →L[ℝ] Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  (h.projectiveWeightChart V e i z).re • Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedFormOperator_pair (i : V.analyticSpace) (n : ℕ)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n) :
    inner ℝ (h.projectiveWeightedFormOperator V e i n z
      (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n a))
        (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n c) =
      (h.projectiveWeightChart V e i z * ((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z : ℂ) *
        Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
          (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) a c)).re := by
  rw [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedFormOperator, _root_.smul_apply, real_inner_smul_left,
    Analysis.HodgeTheory.Decomposition.EuclideanBilinearMetric.Constructions.projectiveWeightedFormOperator_bilinear_pair, ← h.projectiveWeightChart_real V e i z]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedFormOperator_smooth (i : V.analyticSpace) (n : ℕ) :
    ContDiffOn ℝ ∞ (h.projectiveWeightedFormOperator V e i n)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) : Set _) := by
  have hw := Complex.reCLM.contDiff.comp_contDiffOn (h.projectiveWeightChart_smooth V e he i)
  exact hw.smul ((Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he n).mono
    (ConnectionChartDerivative.projectiveOpenChartDomain_le V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedFormOperator_positive (i : V.analyticSpace) (n : ℕ)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (a : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) (ha : a ≠ 0) :
    0 < inner ℝ (h.projectiveWeightedFormOperator V e i n z a) a := by
  rw [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedFormOperator, _root_.smul_apply, real_inner_smul_left,
    h.projectiveWeightChart_apply V e i hz]
  exact mul_pos (h.positive i _) (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.projectiveWeightedFormOperator_positive V e he n z hz.1 a ha)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedFormOperator_isInvertible (i : V.analyticSpace) (n : ℕ)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    (h.projectiveWeightedFormOperator V e i n z).IsInvertible :=
  Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.positiveOperator_isInvertible _ (h.projectiveWeightedFormOperator_positive V e he i n hz)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
