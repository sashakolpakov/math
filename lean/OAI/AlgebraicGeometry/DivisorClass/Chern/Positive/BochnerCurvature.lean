import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseMetricBounds
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.CurvatureBound

/-! # Bochner Curvature -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.BochnerCurvature

noncomputable section

/-! Actual sufficiently positive twists dominate the complete original zeroth-order Bochner curvature contribution on compact projective chart sets. -/

open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem positiveHolomorphicTwistMetric_bochner_curvature_bound
    {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hT : IsCompact T) (hTD : T ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (c : ℝ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ z ∈ T,
      ∀ a : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 0 1 a →
      let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
      let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z
      let F := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 (Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n).curvature.val z
      c * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re ≤
        (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B
          (BaseCurvatureAction.baseCurvatureAction b B (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z a + Line.CurvatureContraction.lineCurvatureAction b B F a) a).re := by
  obtain ⟨C, _, hbase⟩ := Projective.BaseMetricBounds.projectiveBaseCurvatureAction_pair_bound V e he hT hTD
  obtain ⟨N, hN, hline⟩ := ProjectiveLine.CurvatureBound.positiveHolomorphicTwistMetric_curvature_action_lower_bound V u h (C + c)
  refine ⟨N, hN, ?_⟩
  intro n hn z hz a ha
  have hb := (abs_le.mp (hbase z hz a)).1
  have hl := hline n hn e he z (hTD hz) a ha
  dsimp only at hb hl ⊢
  rw [Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_add_left, Complex.add_re]
  nlinarith only [hb, hl]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.BochnerCurvature
