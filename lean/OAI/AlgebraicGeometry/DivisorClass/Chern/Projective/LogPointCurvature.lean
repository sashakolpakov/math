import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogPointPotential
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RealPotentialCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogPositive

/-! # Log Point Curvature -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogPointCurvature

noncomputable section

section

/-! The original global logarithmic point potential has the proved original semipositive curvature wherever its cutoff is identically one near the point. -/

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

theorem projectiveLogPointPotential_curvature_near {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hηz : η =ᶠ[𝓝 z] fun _ => 1) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2
      (ScalarPotential.globalScalarCurvature (LogPointPotential.projectiveLogPointPotential V e he η hη hc hs x m ε hε)).val z =
      extDeriv (fun y => RealScalarOperator.realScalarChernOperator (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
        (fderiv ℝ (RegularizedLogWeight.regularizedNegativeLog x m ε) y)) z := by
  apply RealPotentialCoordinates.projectiveRealScalarPotential_curvature_germ V e he
    (η * RegularizedLogWeight.regularizedNegativeLog x m ε) (hη.mul (RegularizedLogWeight.regularizedNegativeLog_smooth x m hε))
    hc.mul_right (tsupport_mul_subset_left.trans hs) hz _ (RegularizedLogWeight.regularizedNegativeLog_smooth x m hε)
  filter_upwards [hηz] with y hy
  change η y * RegularizedLogWeight.regularizedNegativeLog x m ε y = RegularizedLogWeight.regularizedNegativeLog x m ε y
  rw [hy, one_mul]

theorem projectiveLogPointPotential_curvature_nonneg {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hηz : η =ᶠ[𝓝 z] fun _ => 1) (v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    0 ≤ (Complex.I * Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2
      (ScalarPotential.globalScalarCurvature (LogPointPotential.projectiveLogPointPotential V e he η hη hc hs x m ε hε)).val z ![v, Complex.I • v]).re := by
  rw [projectiveLogPointPotential_curvature_near V e he η hη hc hs x m ε hε hz hηz]
  exact RegularizedLogPositive.regularizedNegativeLog_chern_nonneg x m hε z v

end

/-! The actual global point potential has the full cutoff curvature in original Euclidean chart coordinates, including the transition region. -/

open Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem projectiveLogPointPotential_curvature_full (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2
      (ScalarPotential.globalScalarCurvature (LogPointPotential.projectiveLogPointPotential V e he η hη hc hs x m ε hε)).val z =
      extDeriv (fun y => RealScalarOperator.realScalarChernOperator (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
        (fderiv ℝ (η * RegularizedLogWeight.regularizedNegativeLog x m ε) y)) z :=
  RealPotentialCoordinates.projectiveRealScalarPotential_curvature_germ V e he
    (η * RegularizedLogWeight.regularizedNegativeLog x m ε) (hη.mul (RegularizedLogWeight.regularizedNegativeLog_smooth x m hε))
    hc.mul_right (tsupport_mul_subset_left.trans hs) hz _
    (hη.mul (RegularizedLogWeight.regularizedNegativeLog_smooth x m hε)) Filter.EventuallyEq.rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogPointCurvature
