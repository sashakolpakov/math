import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.LowerBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.BochnerCurvature

/-! # Bochner Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.BochnerPair

noncomputable section

/-! Actual positive twists dominate the original global degree-one Laplacian pairing after subtracting its native rough part. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem positiveHolomorphicTwistMetric_bochner_pair_bound
    {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hT : IsCompact T) (hTD : T ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (c : ℝ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      (Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n).projectiveBochnerPairLowerBound V e T c := by
  obtain ⟨N, hN, hK⟩ := BochnerCurvature.positiveHolomorphicTwistMetric_bochner_curvature_bound V u h e he hT hTD c
  refine ⟨N, hN, ?_⟩
  intro n hn
  exact (Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n).projectiveBochnerPairLowerBound_of_curvature V e he hTD c (hK n hn)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.BochnerPair
