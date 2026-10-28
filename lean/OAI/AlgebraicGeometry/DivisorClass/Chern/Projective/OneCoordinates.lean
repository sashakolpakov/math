import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CovariantDolbeault

/-! # One Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.OneCoordinates

noncomputable section

/-! The original one-form projection in the actual projective covector coordinates. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem oneCovectorPart_eq_of_anti {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 a) :
    (1 / 2 : ℂ) • (a + Complex.I • a.compContinuousLinearMap (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) = a := by
  ext v
  have h := ha AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit v
  simp only [AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit_coe, Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_zero, pow_one, one_mul,
    Complex.star_def, Complex.conj_I] at h
  change (1 / 2 : ℂ) * (a v + Complex.I * a (fun j => Complex.I • v j)) = a v
  rw [h]
  calc
    _ = (1 / 2 : ℂ) * (a v - Complex.I ^ 2 * a v) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem projectiveOpenChartForm_onePart (U : Opens V.analyticSpace) (c : ℂ)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e U) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (Manifold.OneFormProjection.openManifoldOnePart c a).extension z =
      (1 / 2 : ℂ) • (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 a.extension z +
        c • (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 a.extension z).compContinuousLinearMap
          (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) := by
  have hcomm (w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
      ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ) (Complex.I • w) =
      Complex.I • ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ) w :=
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).map_smul Complex.I w
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm
  rw [Manifold.OneFormProjection.openManifoldOnePart_inChart c a e he hz]
  ext v
  simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
    ContinuousLinearMap.lsmul_apply, hcomm]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.OneCoordinates
