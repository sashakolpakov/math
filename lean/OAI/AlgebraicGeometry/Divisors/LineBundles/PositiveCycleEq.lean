import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardFiber
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.DivisorInverse

/-! # Positive Cycle Eq -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.PositiveCycleEq.BundleCycles.PositiveCycle

noncomputable section

/-! The positive part of a finite rational cycle records its zeros.
An injective model with unchanged residue fields, nonnegative orders, and
coverage of every positive coefficient pushes to exactly that part. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

def positivePart {α : Type*} (c : α →₀ ℚ) : α →₀ ℚ :=
  Finsupp.mapRange (fun a => max a 0) (by simp) c

theorem positivePart_apply {α : Type*} (c : α →₀ ℚ) (x : α) :
    positivePart c x = max (c x) 0 := rfl

theorem positivePart_sub_neg {α : Type*} (c : α →₀ ℚ) :
    positivePart c - positivePart (-c) = c := by
  ext x
  exact max_zero_sub_max_neg_zero_eq_self (c x)

theorem pointPushforward_eq_positivePart {X Y : Scheme} (i : X ⟶ Y)
    (hi : Function.Injective i) (hd : ∀ x : X, i.residueDegree x = 1)
    (c : X →₀ ℚ) (d : Y →₀ ℚ)
    (hc : ∀ x : X, c x = d (i x)) (hn : ∀ x : X, 0 ≤ c x)
    (hcover : ∀ y : Y, 0 < d y → y ∈ Set.range i) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i c = positivePart d := by
  ext y
  by_cases hy : y ∈ Set.range i
  · obtain ⟨x, rfl⟩ := hy
    rw [IntersectionTheory.ProjectionFormula.PushforwardFiber.pointPushforward_uniqueFiber i x (i x) rfl
      (fun z hz => hi hz), hd, Nat.cast_one, mul_one, positivePart_apply, ← hc]
    exact (max_eq_left (hn x)).symm
  · rw [IntersectionTheory.ProjectionFormula.PushforwardFiber.pointPushforward_apply_eq_zero i c y
      (fun x _ hx => hy ⟨x, hx⟩), positivePart_apply]
    exact (max_eq_right (le_of_not_gt (fun hp => hy (hcover y hp)))).symm

theorem principalDivisor_eq_positive_sub_inverse {X : Scheme} [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (g : X.functionField) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g = positivePart (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) -
      positivePart (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g⁻¹) := by
  rw [Principal.DivisorInverse.BundleCycles.PrincipalDivisorInverse.rationalPrincipalPointDivisor_inv, positivePart_sub_neg]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.PositiveCycleEq.BundleCycles.PositiveCycle
