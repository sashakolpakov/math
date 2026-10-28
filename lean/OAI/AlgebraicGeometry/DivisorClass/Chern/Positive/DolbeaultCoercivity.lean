import OAI.AlgebraicGeometry.DivisorClass.Chern.BaseCutoffGlobal

/-! # Dolbeault Coercivity -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.DolbeaultCoercivity

noncomputable section

/-! The original degree-one smooth Dolbeault energy is coercive for all sufficiently positive actual holomorphic twists. -/

open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem positiveHolomorphicTwistMetric_smooth_coercive :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      (Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n).smoothDolbeaultOneCoercive V := by
  obtain ⟨N, hN, hB⟩ := Projective.BaseCutoffBounds.positiveHolomorphicTwistMetric_all_base_cutoffs V u h (Projective.BaseCutoffBounds.projectiveBaseTotalCutoffErrorBound V + 1)
  refine ⟨N, hN, ?_⟩
  intro n hn
  exact (Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n).smoothDolbeaultOneCoercive_of_base_cutoffs V (hB n hn)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.DolbeaultCoercivity
