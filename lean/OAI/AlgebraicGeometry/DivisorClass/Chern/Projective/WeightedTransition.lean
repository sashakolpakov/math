import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CovectorTransition
import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorMetricRe

/-! # Weighted Transition -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Actual metric weights cancel the original bundle transition in every covector pairing. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightChart_transition (i j : V.analyticSpace)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i ⊓
        Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j)) :
    h.projectiveWeightChart V e i z =
      (Complex.normSq (Projective.FrameScalarGlue.projectiveTransitionChart V u e i j z) : ℂ) * h.projectiveWeightChart V e j z := by
  rw [h.projectiveWeightChart_apply V e i ⟨hz.1, hz.2.1⟩,
    h.projectiveWeightChart_apply V e j ⟨hz.1, hz.2.2⟩,
    Projective.FrameScalarGlue.projectiveTransitionChart_apply V u e i j hz, h.transition i j _ hz.2.1 hz.2.2, Complex.ofReal_mul]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedPair_transition
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    (i j : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i ⊓
        Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j))) :
    h.projectiveWeightChart V e j z *
        Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
          (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val j).extension z)
          (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (c.val j).extension z) =
      h.projectiveWeightChart V e i z *
        Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
          (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension z)
          (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (c.val i).extension z) := by
  rw [Projective.FrameScalarGlue.holomorphicLineSmoothForm_transition_chart V u e U n a i j hz,
    Projective.FrameScalarGlue.holomorphicLineSmoothForm_transition_chart V u e U n c i j hz]
  exact TensorMetricRe.bilinearFormMetricPair_weighted_gauge _ n _ _ _ _ _ _
    (h.projectiveWeightChart_transition V e i j ⟨hz.1, hz.2.2⟩)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
