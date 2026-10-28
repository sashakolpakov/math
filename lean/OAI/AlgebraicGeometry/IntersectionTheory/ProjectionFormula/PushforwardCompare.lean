import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalPrincipalDivisor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle

/-! # Pushforward Compare -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardCompare

noncomputable section

/-! Cycle pushforward ignores coefficients at zero-degree points.
This permits the relative zero-parameter calculation to cover precisely
the points with positive coefficients that contribute to pushforward. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle

theorem pointPushforward_congr {X Y : Scheme} (f : X ⟶ Y) (c d : X →₀ ℚ)
    (h : ∀ x : X, f.residueDegree x ≠ 0 → c x = d x) :
    CyclePushforward.pointPushforward f c = CyclePushforward.pointPushforward f d := by
  have hz : CyclePushforward.pointPushforward f (c - d) = 0 := by
    ext y
    apply BirationalPrincipalDivisor.pointPushforward_eq_zero_of_degrees
    intro x hx _
    by_contra hd
    exact hx (by simp only [Finsupp.sub_apply, h x hd, sub_self])
  rw [map_sub, sub_eq_zero] at hz
  exact hz

theorem positivePart_model {A X Y : Scheme} (i : A ⟶ X) (f : X ⟶ Y)
    (hi : Function.Injective i) (hd : ∀ a : A, i.residueDegree a = 1)
    (c : A →₀ ℚ) (d : X →₀ ℚ)
    (hc : ∀ a : A, c a = d (i a)) (hn : ∀ a : A, 0 ≤ c a)
    (hcover : ∀ x : X, f.residueDegree x ≠ 0 → 0 < d x → x ∈ Set.range i) :
    CyclePushforward.pointPushforward f (PositiveCycle.positivePart d) = CyclePushforward.pointPushforward (i ≫ f) c := by
  have hp : CyclePushforward.pointPushforward f (PositiveCycle.positivePart d) = CyclePushforward.pointPushforward f (CyclePushforward.pointPushforward i c) := by
    apply pointPushforward_congr
    intro x hx
    by_cases hxi : x ∈ Set.range i
    · obtain ⟨a, rfl⟩ := hxi
      rw [PushforwardFiber.pointPushforward_uniqueFiber i a (i a) rfl (fun b hb => hi hb),
        hd, Nat.cast_one, mul_one, PositiveCycle.positivePart_apply, ← hc]
      exact max_eq_left (hn a)
    · rw [PushforwardFiber.pointPushforward_apply_eq_zero i c x
        (fun a _ ha => hxi ⟨a, ha⟩), PositiveCycle.positivePart_apply]
      exact max_eq_right (le_of_not_gt (fun hpos => hxi (hcover x hx hpos)))
  exact hp.trans (DFunLike.congr_fun (CyclePushforward.pointPushforward_comp i f) c).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardCompare
