import OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalRealScalarForm
import OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogWeight
import OAI.AlgebraicGeometry.DivisorClass.Chern.RealChartExtension
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Potential

/-! # Log Point Potential -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogPointPotential

noncomputable section

/-! Constructed original global smooth logarithmic point potentials, with their exact chart values and actual metric weights. -/

open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
  (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
  (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (m : ℕ) (ε : ℝ) (hε : 0 < ε)

def projectiveLogPointPotential : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 :=
  GlobalRealScalarForm.globalRealScalarForm (RealChartExtension.projectiveRealChartExtension V e (η * RegularizedLogWeight.regularizedNegativeLog x m ε))
    (RealChartExtension.projectiveRealChartExtension_smooth V e he _ (hη.mul (RegularizedLogWeight.regularizedNegativeLog_smooth x m hε))
      hc.mul_right (tsupport_mul_subset_left.trans hs))

theorem projectiveLogPointPotential_real :
    ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (projectiveLogPointPotential V e he η hη hc hs x m ε hε) =
      projectiveLogPointPotential V e he η hη hc hs x m ε hε :=
  GlobalRealScalarForm.globalRealScalarForm_real _ _

theorem projectiveLogPointPotential_scalar {y : V.analyticSpace} (hy : y ∈ e.source) :
    ScalarPotentialFunctions.realPotentialScalar (projectiveLogPointPotential V e he η hη hc hs x m ε hε) y =
      η (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e y) * RegularizedLogWeight.regularizedNegativeLog x m ε (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e y) :=
  (GlobalRealScalarForm.globalRealScalarForm_scalar _ _ y).trans (RealChartExtension.projectiveRealChartExtension_apply V e _ hy)

theorem projectiveLogPointPotential_exp_one {y : V.analyticSpace} (hy : y ∈ e.source)
    (hηy : η (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e y) = 1) :
    Real.exp (ScalarPotentialFunctions.realPotentialScalar (projectiveLogPointPotential V e he η hη hc hs x m ε hε) y) =
      ((ε + ‖Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e y - x‖ ^ 2) ^ m)⁻¹ := by
  rw [projectiveLogPointPotential_scalar V e he η hη hc hs x m ε hε hy, hηy, one_mul]
  exact RegularizedLogWeight.regularizedNegativeLog_exp x m hε _

theorem projectiveLogPointPotential_metric_weight
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (i : V.analyticSpace) (y : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
    (hy : y.val ∈ e.source) (hηy : η (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e y.val) = 1) :
    (h.withPotential (projectiveLogPointPotential V e he η hη hc hs x m ε hε)).weight i y =
      ((ε + ‖Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e y.val - x‖ ^ 2) ^ m)⁻¹ * h.weight i y :=
  congrArg (fun r : ℝ => r * h.weight i y)
    (projectiveLogPointPotential_exp_one V e he η hη hc hs x m ε hε hy hηy)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogPointPotential
