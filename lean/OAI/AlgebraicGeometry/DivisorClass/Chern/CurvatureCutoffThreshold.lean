import OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.BochnerPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.BochnerCutoffLowerBound

/-! # Curvature Cutoff Threshold -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CurvatureCutoffThreshold

noncomputable section

/-! A bound depending only on the original base chart converts any actual bundle curvature lower bound to the original cutoff coercivity estimate. -/

open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem projective_exists_curvature_cutoff_threshold (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
      (h : HolomorphicMetric.Data.HolomorphicLineMetricData u),
      (∀ (x : V.analyticSpace) (v : TangentSpace 𝓘(ℝ, V.analyticModel) x), v ≠ 0 →
        (C + c) * (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re ≤
          ((Complex.I • h.curvature) x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re) →
      h.projectiveBochnerCutoffLowerBound V e η c := by
  let baseBound := Projective.BaseMetricBounds.projectiveBaseCurvatureAction_pair_bound V e he hc.isCompact hs
  refine ⟨baseBound.choose, baseBound.choose_spec.1, ?_⟩
  intro u h hF
  apply h.projectiveBochnerCutoffLowerBound_of_pair V e he η hη hc hs c
  apply h.projectiveBochnerPairLowerBound_of_curvature V e he hs c
  intro z hz a ha
  have hb := (abs_le.mp (baseBound.choose_spec.2 z hz a)).1
  have hl := ProjectiveLine.CurvatureBound.projective_line_curvature_action_lower_bound V e he h.curvature
    (baseBound.choose + c) hF (hs hz) a ha
  dsimp only at hb hl ⊢
  rw [Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_add_left, Complex.add_re]
  nlinarith only [hb, hl]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CurvatureCutoffThreshold
