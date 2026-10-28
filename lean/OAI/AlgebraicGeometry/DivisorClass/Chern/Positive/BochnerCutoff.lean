import OAI.AlgebraicGeometry.DivisorClass.Chern.BochnerCutoffLowerBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.BochnerPair

/-! # Bochner Cutoff -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.BochnerCutoff

noncomputable section

/-! Actual sufficiently positive twists satisfy the original degree-one Laplacian cutoff estimate. -/

open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem positiveHolomorphicTwistMetric_bochner_cutoff_bound
    (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (c : ℝ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      (Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n).projectiveBochnerCutoffLowerBound V e η c := by
  obtain ⟨N, hN, hB⟩ := BochnerPair.positiveHolomorphicTwistMetric_bochner_pair_bound V u h e he hc.isCompact hs c
  refine ⟨N, hN, ?_⟩
  intro n hn
  exact (Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n).projectiveBochnerCutoffLowerBound_of_pair V e he η hη hc hs c (hB n hn)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.BochnerCutoff
