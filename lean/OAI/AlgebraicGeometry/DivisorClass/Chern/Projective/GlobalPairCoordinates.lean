import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.VariableMetricIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.WeightedTransition
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveMetricCompatibility

/-! # Global Pair Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original global bundle metric pairing, including the original volume density, in any base chart and line frame. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.ProjectiveMetricCompatibility.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveGlobalPair (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z : ℂ) * h.globalFormPair V n a c (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveGlobalPair_inFrame (n : ℕ)
    (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    h.projectiveGlobalPair V e n a c z = (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z : ℂ) *
      (h.projectiveWeightChart V e i z *
        Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
          (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension z)
          (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (c.val i).extension z)) := by
  rw [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveGlobalPair, h.globalFormPair_inFrame V n a c i (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) hz.2,
    h.projectiveWeightChart_apply V e i hz,
    ← Analysis.HodgeTheory.Decomposition.ProjectiveMetricCompatibility.Constructions.projectivePointPair_eq_bilinearFormMetricPair V e he n (a.val i).extension (c.val i).extension hz.1,
    Projective.CovectorPair.projectiveFormPointPair_eq_tangentPair,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply (a.val i) ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, trivial, hz.2⟩,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply (c.val i) ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, trivial, hz.2⟩]
  rfl

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveGlobalPair_self_nonneg (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) : 0 ≤ (h.projectiveGlobalPair V e n a a z).re := by
  simp only [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveGlobalPair, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_pos V e he hz).le (h.globalFormPair_nonneg V n a _)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
