import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.DivisorInverse

/-! # Positive Cycle -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle

/-! The positive part of a finite rational cycle records its zeros.
An injective model with unchanged residue fields, nonnegative orders, and
coverage of every positive coefficient pushes to exactly that part. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm

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
    CyclePushforward.pointPushforward i c = positivePart d := by
  ext y
  by_cases hy : y ∈ Set.range i
  · obtain ⟨x, rfl⟩ := hy
    rw [PushforwardFiber.pointPushforward_uniqueFiber i x (i x) rfl
      (fun z hz => hi hz), hd, Nat.cast_one, mul_one, positivePart_apply, ← hc]
    exact (max_eq_left (hn x)).symm
  · rw [PushforwardFiber.pointPushforward_apply_eq_zero i c y
      (fun x _ hx => hy ⟨x, hx⟩), positivePart_apply]
    exact (max_eq_right (le_of_not_gt (fun hp => hy (hcover y hp)))).symm

theorem principalDivisor_eq_positive_sub_inverse {X : Scheme} [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (g : X.functionField) :
    Affine.DivisorNorm.rationalPrincipalDivisor X g = positivePart (Affine.DivisorNorm.rationalPrincipalDivisor X g) -
      positivePart (Affine.DivisorNorm.rationalPrincipalDivisor X g⁻¹) := by
  rw [Principal.DivisorInverse.rationalPrincipalDivisor_inv, positivePart_sub_neg]

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle.Pushforward

/-! Positive parts commute with native residue-degree pushforward
whenever all coefficients in each fiber have the same sign. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle

theorem coefficient_congr {Z X : Scheme} (f : Z ⟶ X) (c d : Z →₀ ℚ) (x : X)
    (h : ∀ z, f z = x → c z = d z) : CyclePushforward.pointPushforward f c x = CyclePushforward.pointPushforward f d x := by
  have hz : CyclePushforward.pointPushforward f (c - d) x = 0 := by
    apply PushforwardFiber.pointPushforward_apply_eq_zero
    intro z hz he
    exact hz (by rw [Finsupp.sub_apply, h z he, sub_self])
  rw [map_sub, Finsupp.sub_apply, sub_eq_zero] at hz
  exact hz

theorem nonneg_at {Z X : Scheme} (f : Z ⟶ X) (c : Z →₀ ℚ) (x : X)
    (h : ∀ z, f z = x → 0 ≤ c z) : 0 ≤ CyclePushforward.pointPushforward f c x := by
  rw [CyclePushforward.pointPushforward, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  apply Finset.sum_nonneg
  intro z _
  rw [Finsupp.smul_apply, smul_eq_mul]
  by_cases hz : f z = x
  · rw [hz, Finsupp.single_eq_same]
    exact mul_nonneg (h z hz) (Nat.cast_nonneg _)
  · rw [Finsupp.single_eq_of_ne (fun h => hz h.symm), mul_zero]

theorem nonpos_at {Z X : Scheme} (f : Z ⟶ X) (c : Z →₀ ℚ) (x : X)
    (h : ∀ z, f z = x → c z ≤ 0) : CyclePushforward.pointPushforward f c x ≤ 0 := by
  have hn := nonneg_at f (-c) x (fun z hz => by
    rw [Finsupp.neg_apply]
    exact neg_nonneg.mpr (h z hz))
  rw [map_neg, Finsupp.neg_apply, neg_nonneg] at hn
  exact hn

theorem positivePart_comm {Z X : Scheme} (f : Z ⟶ X) (c : Z →₀ ℚ)
    (h : ∀ x : X, (∀ z, f z = x → 0 ≤ c z) ∨ (∀ z, f z = x → c z ≤ 0)) :
    CyclePushforward.pointPushforward f (positivePart c) = positivePart (CyclePushforward.pointPushforward f c) := by
  apply Finsupp.ext
  intro x
  rw [positivePart_apply]
  rcases h x with hp | hn
  · have he := coefficient_congr f (positivePart c) c x (fun z hz => max_eq_left (hp z hz))
    rw [he, max_eq_left (nonneg_at f c x hp)]
  · have hz : CyclePushforward.pointPushforward f (positivePart c) x = 0 := by
      apply PushforwardFiber.pointPushforward_apply_eq_zero
      intro z hz he
      exact hz (max_eq_right (hn z he))
    rw [hz, max_eq_right (nonpos_at f c x hn)]

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle.Pushforward

end

end OAI
