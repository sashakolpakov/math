import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.NeighborhoodTest
import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionChartDerivative

/-! # Point Log Cutoff -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PointLogCutoff

noncomputable section

/-! A fixed original base-chart cutoff for a prescribed point, constructed independently of every bundle, metric, twist, and regularization parameter. -/

open Set Filter
open scoped ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hx : x ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

def projectivePointLogCutoff : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ :=
  (Compact.NeighborhoodTest.exists_real_coefficient_cutoff (isCompact_singleton (x := x)) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
    (singleton_subset_iff.mpr hx)).choose

theorem projectivePointLogCutoff_smooth : ContDiff ℝ ∞ (projectivePointLogCutoff V e x hx) :=
  (Compact.NeighborhoodTest.exists_real_coefficient_cutoff (isCompact_singleton (x := x)) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
    (singleton_subset_iff.mpr hx)).choose_spec.1

theorem projectivePointLogCutoff_compact : HasCompactSupport (projectivePointLogCutoff V e x hx) :=
  (Compact.NeighborhoodTest.exists_real_coefficient_cutoff (isCompact_singleton (x := x)) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
    (singleton_subset_iff.mpr hx)).choose_spec.2.1

theorem projectivePointLogCutoff_support : tsupport (projectivePointLogCutoff V e x hx) ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e :=
  (Compact.NeighborhoodTest.exists_real_coefficient_cutoff (isCompact_singleton (x := x)) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
    (singleton_subset_iff.mpr hx)).choose_spec.2.2.1

theorem projectivePointLogCutoff_one_near : projectivePointLogCutoff V e x hx =ᶠ[𝓝 x] fun _ => 1 :=
  (Compact.NeighborhoodTest.exists_real_coefficient_cutoff (isCompact_singleton (x := x)) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
    (singleton_subset_iff.mpr hx)).choose_spec.2.2.2 x (mem_singleton x)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PointLogCutoff
