import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogPointCurvature
import OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarCurvatureZero
import OAI.AlgebraicGeometry.DivisorClass.Chern.RealChartExtension

/-! # Log Curvature Support -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogCurvatureSupport

noncomputable section

/-! The original logarithmic point curvature vanishes off the actual cutoff support and outside the original chart. -/

open Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
  (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
  (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (m : ℕ) (ε : ℝ) (hε : 0 < ε)

theorem projectiveLogPointPotential_curvature_zero_off_cutoff {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (hzη : z ∉ tsupport η) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2
      (ScalarPotential.globalScalarCurvature (LogPointPotential.projectiveLogPointPotential V e he η hη hc hs x m ε hε)).val z = 0 := by
  have hz0 : η * RegularizedLogWeight.regularizedNegativeLog x m ε =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzη] with y hy
    change η y = 0 at hy
    change η y * RegularizedLogWeight.regularizedNegativeLog x m ε y = 0
    rw [hy, zero_mul]
  exact (RealPotentialCoordinates.projectiveRealScalarPotential_curvature_germ V e he
    (η * RegularizedLogWeight.regularizedNegativeLog x m ε) (hη.mul (RegularizedLogWeight.regularizedNegativeLog_smooth x m hε))
    hc.mul_right (tsupport_mul_subset_left.trans hs) hz _ contDiff_const hz0).trans
      (ScalarCurvatureZero.realScalarChern_curvature_zero z)

theorem projectiveLogPointPotential_curvature_zero_off_chart {y : V.analyticSpace} (hy : y ∉ e.source) :
    ScalarPotential.globalScalarCurvature (LogPointPotential.projectiveLogPointPotential V e he η hη hc hs x m ε hε) y = 0 := by
  apply ScalarCurvatureZero.globalRealScalarForm_curvature_zero_of_germ
  apply notMem_tsupport_iff_eventuallyEq.mp
  intro hys
  exact hy (ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e (tsupport_mul_subset_left.trans hs)
    (RealChartExtension.projectiveRealChartExtension_tsupport V e (η * RegularizedLogWeight.regularizedNegativeLog x m ε) hc.mul_right
      (tsupport_mul_subset_left.trans hs) hys))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogCurvatureSupport
