import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

/-! # Pushforward Coefficient Congruence -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardCoefficientCongruence

noncomputable section

/-! A pushforward coefficient only depends on source coefficients with
the specified image support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

theorem eq {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (a b : X.RationalDimensionCycle p) (C : Y.DimensionCycleSupport q)
    (h : ∀ D : X.DimensionCycleSupport p, ProperCycleLinearity.imageSupport f D.val = C.val → a D = b D) :
    ProperCycleLinearity.cyclePushforward f p q a C = ProperCycleLinearity.cyclePushforward f p q b C := by
  apply sub_eq_zero.mp
  change (ProperCycleLinearity.cyclePushforward f p q a - ProperCycleLinearity.cyclePushforward f p q b) C = 0
  rw [← map_sub]
  simp only [ProperCycleLinearity.cyclePushforward, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, ProperCycleLinearity.cyclePushforwardGenerator_apply]
  apply Finset.sum_eq_zero
  intro D _
  by_cases he : ProperCycleLinearity.imageSupport f D.val = C.val
  · rw [Finsupp.sub_apply, h D he, sub_self, zero_smul]
  · rw [ite_eq_right he, smul_zero]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardCoefficientCongruence
