import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardFiber

/-! # Point Pushforward Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointPushforwardSupport

noncomputable section

/-! Every nonzero pushforward coefficient comes from an actual
point in the support of the finite source cycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_point {Y Z : Scheme} (f : Y ⟶ Z) (c : Y →₀ ℚ) (z : Z)
    (hz : CyclePushforward.pointPushforward f c z ≠ 0) :
    ∃ y : Y, c y ≠ 0 ∧ f y = z := by
  by_contra hn
  push Not at hn
  exact hz (PushforwardFiber.pointPushforward_apply_eq_zero f c z hn)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointPushforwardSupport
