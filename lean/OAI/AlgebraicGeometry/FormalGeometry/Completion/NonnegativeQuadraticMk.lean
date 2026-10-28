import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-! # Nonnegative Quadratic Mk -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.NonnegativeQuadraticMk.Construction

noncomputable section

/-! The zero set of a nonnegative rational quadratic function is a saturated
subgroup, and translation by that subgroup preserves the function. -/

universe u

structure NonnegativeQuadratic (G : Type u) [AddCommGroup G] where
  value : G → ℚ
  zero : value 0 = 0
  nonneg : ∀ x, 0 ≤ value x
  parallelogram : ∀ x y, value (x + y) + value (x - y) = 2 * (value x + value y)

namespace NonnegativeQuadratic

variable {G : Type u} [AddCommGroup G] (q : NonnegativeQuadratic G)

theorem neg (x : G) : q.value (-x) = q.value x := by
  have h := q.parallelogram 0 x
  rw [zero_add, zero_sub, q.zero] at h
  linarith

def zeroKernel : AddSubgroup G where
  carrier := {x | q.value x = 0}
  zero_mem' := q.zero
  add_mem' := by
    intro x y hx hy
    have h := q.parallelogram x y
    have hp := q.nonneg (x + y)
    have hm := q.nonneg (x - y)
    change q.value x = 0 at hx
    change q.value y = 0 at hy
    change q.value (x + y) = 0
    linarith
  neg_mem' := by
    intro x hx
    exact (q.neg x).trans hx

theorem nsmul (n : ℕ) (x : G) : q.value (n • x) = (n : ℚ) ^ 2 * q.value x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [q.zero]
  | one => simp
  | more n hn hn1 =>
    have hp := q.parallelogram ((n + 1) • x) x
    have hadd : (n + 1) • x + x = (n + 2) • x := by simp [add_nsmul, two_nsmul, add_assoc]
    have hsub : (n + 1) • x - x = n • x := by simp [add_nsmul]
    rw [hadd, hsub, hn, hn1] at hp
    push_cast at hp ⊢
    nlinarith

theorem nsmul_mem_zeroKernel_iff (n : ℕ) (hn : 0 < n) (x : G) :
    n • x ∈ q.zeroKernel ↔ x ∈ q.zeroKernel := by
  change q.value (n • x) = 0 ↔ q.value x = 0
  rw [q.nsmul, mul_eq_zero]
  have h : (n : ℚ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hn.ne')
  exact or_iff_right h

theorem translate_nsmul_of_zero (x y : G) (hy : q.value y = 0) (n : ℕ) :
    q.value (x + n • y) = q.value x + (n : ℚ) * (q.value (x + y) - q.value x) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n hn hn1 =>
    have hp := q.parallelogram (x + (n + 1) • y) y
    have hadd : (x + (n + 1) • y) + y = x + (n + 2) • y := by
      simp [add_nsmul, two_nsmul, add_assoc]
    have hsub : (x + (n + 1) • y) - y = x + n • y := by
      simp only [add_nsmul, one_nsmul]
      abel
    rw [hadd, hsub, hn, hn1, hy] at hp
    push_cast at hp ⊢
    linarith

private theorem slope_nonneg (a b : ℚ) (h : ∀ n : ℕ, 0 ≤ a + n * b) : 0 ≤ b := by
  by_contra hb
  have hneg : 0 < -b := neg_pos.mpr (lt_of_not_ge hb)
  obtain ⟨n, hn⟩ := exists_nat_gt (a / (-b))
  have hn' : a < (n : ℚ) * (-b) := (div_lt_iff₀ hneg).mp hn
  have hh := h n
  nlinarith

theorem translate_of_zero (x y : G) (hy : q.value y = 0) : q.value (x + y) = q.value x := by
  have hp : 0 ≤ q.value (x + y) - q.value x :=
    slope_nonneg _ _ (fun n => (q.translate_nsmul_of_zero x y hy n) ▸ q.nonneg (x + n • y))
  have hny : q.value (-y) = 0 := (q.neg y).trans hy
  have hm : 0 ≤ q.value (x - y) - q.value x := by
    have h := slope_nonneg (q.value x) (q.value (x + -y) - q.value x)
      (fun n => (q.translate_nsmul_of_zero x (-y) hny n) ▸ q.nonneg (x + n • (-y)))
    simpa only [sub_eq_add_neg] using h
  have h := q.parallelogram x y
  rw [hy] at h
  linarith

def quotientValue : G ⧸ q.zeroKernel → ℚ :=
  Quotient.lift q.value (by
    intro x y h
    have hy : q.value (-x + y) = 0 := QuotientAddGroup.leftRel_apply.mp h
    have hh := q.translate_of_zero x (-x + y) hy
    simpa only [add_neg_cancel_left] using hh.symm)

theorem quotientValue_mk (x : G) : q.quotientValue (QuotientAddGroup.mk x) = q.value x := rfl

end NonnegativeQuadratic

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.NonnegativeQuadraticMk.Construction
