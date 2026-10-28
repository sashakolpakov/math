import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.DolbeaultBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.DolbeaultExact
import OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.DolbeaultCoercivity

/-! # Smooth Dolbeault -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Every sufficiently positive actual twist has original smooth Dolbeault primitives with a uniform bound in its own actual metric. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

def HolomorphicMetric.Data.HolomorphicLineMetricData.hasBoundedSmoothDolbeaultPrimitives : Prop :=
  ∀ a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1, HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a = 0 →
    ∃ b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 0, HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 b = a ∧
      ‖Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 b.val‖ ≤ ‖Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a‖

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.hasBoundedSmoothDolbeaultPrimitives_of_coercive
    (hc : h.smoothDolbeaultOneCoercive V) : h.hasBoundedSmoothDolbeaultPrimitives V :=
  HolomorphicSmooth.DolbeaultBound.holomorphicMetricSmoothDolbeault_solve_bound V h hc

theorem Positive.SmoothDolbeault.positiveHolomorphicTwistMetric_smooth_dolbeault :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      (Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n).hasBoundedSmoothDolbeaultPrimitives V := by
  obtain ⟨N, hN, hC⟩ := Positive.DolbeaultCoercivity.positiveHolomorphicTwistMetric_smooth_coercive V u h
  exact ⟨N, hN, fun n hn =>
    (Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n).hasBoundedSmoothDolbeaultPrimitives_of_coercive V (hC n hn)⟩

include h in
theorem Positive.SmoothDolbeault.positiveHolomorphicTwistMetric_dolbeault_one_exact :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      LinearMap.ker (HolomorphicLine.Dolbeault.holomorphicLineDolbeault (u + n • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) ⊤ 1) =
        LinearMap.range (HolomorphicLine.Dolbeault.holomorphicLineDolbeault (u + n • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) ⊤ 0) :=
  ⟨(Positive.DolbeaultCoercivity.positiveHolomorphicTwistMetric_smooth_coercive V u h).choose,
    (Positive.DolbeaultCoercivity.positiveHolomorphicTwistMetric_smooth_coercive V u h).choose_spec.1,
    fun n hn => HolomorphicSmooth.DolbeaultExact.holomorphicMetricSmoothDolbeault_one_exact V
      (Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n)
      ((Positive.DolbeaultCoercivity.positiveHolomorphicTwistMetric_smooth_coercive V u h).choose_spec.2 n hn)⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
