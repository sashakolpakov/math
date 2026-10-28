import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CurvaturePair
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.PositiveCurvature
import OAI.Analysis.HodgeTheory.Decomposition.EuclideanForms
import OAI.Analysis.HodgeTheory.Decomposition.EuclideanMetricDerivative

/-! # Curvature Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.CurvatureBound

noncomputable section

/-! Actual positive twisting metrics give the pointwise curvature-action lower bound in every original projective chart. -/

open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem smoothForm_euclidean_two_at (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    let x := e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)
    let w := Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap e (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V v)
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 F.val z ![v, Complex.I • v] = F x ![w, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I w] := by
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
  apply congrArg (F _)
  funext j
  fin_cases j
  · rfl
  · change Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap e (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V (Complex.I • v)) = _
    rw [(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).map_smul, Analysis.DifferentialForms.Manifold.CovectorAction.complexTangentSMul_chartInverse e he hz]
    rfl

theorem projective_line_curvature_coordinate_lower_bound
    (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2) (c : ℝ)
    (hF : ∀ (x : V.analyticSpace) (v : TangentSpace 𝓘(ℝ, V.analyticModel) x), v ≠ 0 →
      c * (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re ≤
        ((Complex.I • F) x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    c * ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z v v ≤
      (Complex.I * Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 F.val z ![v, Complex.I • v]).re := by
  by_cases hv : v = 0
  · subst v
    simp only [map_zero, mul_zero, smul_zero]
    rw [← AntiTwoFormCoefficients.twoFormBilinear_apply, Line.CurvaturePair.twoFormBilinear_self]
    simp
  let x := e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)
  let w := Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap e (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V v)
  have hw : w ≠ 0 := by
    intro hw
    have ht := congrArg (fun T => T (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V v)) (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap_comp_inverse e he hz)
    change Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x w = ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V v at ht
    rw [hw, map_zero] at ht
    exact hv ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).injective (ht.symm.trans (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).map_zero.symm))
  have hp := hF x w hw
  rw [ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric, ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.metricFromTwoForm_apply]
  change c * (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V).val z ![v, Complex.I • v]).re ≤ _
  rw [smoothForm_euclidean_two_at V e he (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V) hz v,
    smoothForm_euclidean_two_at V e he F hz v]
  exact hp

theorem projective_line_curvature_action_lower_bound
    (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2) (c : ℝ)
    (hF : ∀ (x : V.analyticSpace) (v : TangentSpace 𝓘(ℝ, V.analyticModel) x), v ≠ 0 →
      c * (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re ≤
        ((Complex.I • F) x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (a : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 0 1 a) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z
    c * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re ≤
      (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B (Line.CurvatureContraction.lineCurvatureAction b B (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 F.val z) a) a).re :=
  Line.CurvaturePair.lineCurvatureAction_lower_bound _ _ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz)
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz) (Analysis.HodgeTheory.Decomposition.EuclideanMetricDerivative.Constructions.projectiveEuclideanMetric_J_skew V e he hz) _ a ha c
    (projective_line_curvature_coordinate_lower_bound V e he F c hF hz)

omit he in
theorem positiveHolomorphicTwistMetric_curvature_action_lower_bound
    (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (c : ℝ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel), e ∈ atlas V.analyticModel V.analyticSpace →
      ∀ z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e, ∀ a : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1,
      Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 0 1 a →
      let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
      let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z
      c * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re ≤
        (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B (Line.CurvatureContraction.lineCurvatureAction b B
          (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 (Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n).curvature.val z) a) a).re := by
  obtain ⟨N, hN, hp⟩ := Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric_projective_lower_bound V u h c
  refine ⟨N, hN, ?_⟩
  intro n hn f hf z hz a ha
  exact projective_line_curvature_action_lower_bound V f hf _ c
    (fun x v hv => (hp n hn x v hv).le) hz a ha

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.CurvatureBound
