import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrimePowerBinomialLinearization
import Mathlib.Algebra.Group.Torsion

/-! # Prime Order Congruence Inflation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrimeOrderCongruenceInflation

noncomputable section

/-! Prime-order congruences deepen in additively torsion-free rings, starting at an odd prime or at the square of two. -/

universe u

variable {R : Type u} [Ring R] [IsAddTorsionFree R]

theorem primeOrder_congruence_step (u : R) (q r : ℕ) (hq : q.Prime) (hr : 0 < r)
    (hsize : r + 2 ≤ r * q) (hu : u ^ q = 1) (x : R) (hx : (q ^ r) • x = u - 1) :
    ∃ y : R, (q ^ (r + 1)) • y = u - 1 := by
  have he : u = 1 + (q ^ r) • x := by rw [hx]; abel
  obtain ⟨z, hz⟩ := PrimePowerBinomialLinearization.primePower_binomialLinearization x q r hq hr hsize
  have hh : (1 : R) + (q ^ (r + 1)) • x + (q ^ (r + 2)) • z = 1 :=
    hz.symm.trans ((congrArg (fun a : R => a ^ q) he).symm.trans hu)
  have hzero : (q ^ (r + 1)) • x + (q ^ (r + 2)) • z = 0 :=
    add_left_cancel ((add_assoc (1 : R) _ _).symm.trans (hh.trans (add_zero (1 : R)).symm))
  have hf : (q ^ (r + 1)) • (x + q • z) = 0 := by
    rw [nsmul_add, ← mul_smul, ← pow_succ]
    exact hzero
  have hxz : x = q • (-z) :=
    (eq_neg_of_add_eq_zero_left ((nsmul_eq_zero_iff_right (pow_ne_zero _ hq.ne_zero)).mp hf)).trans
      (smul_neg q z).symm
  refine ⟨-z, ?_⟩
  rw [pow_succ, mul_smul, ← hxz]
  exact hx

theorem primeOrder_congruence_depths (u : R) (q r : ℕ) (hq : q.Prime) (hr : 0 < r)
    (hsize : r + 2 ≤ r * q) (hu : u ^ q = 1) (h : ∃ x : R, (q ^ r) • x = u - 1) (k : ℕ) :
    ∃ y : R, (q ^ (r + k)) • y = u - 1 := by
  induction k with
  | zero => simpa only [Nat.add_zero] using h
  | succ k ih =>
    obtain ⟨x, hx⟩ := ih
    have hk : k * 2 ≤ k * q := Nat.mul_le_mul_left k hq.two_le
    have hs : r + k + 2 ≤ (r + k) * q := by nlinarith
    exact primeOrder_congruence_step u q (r + k) hq (by omega) hs hu x hx

theorem primeOrder_congruence_allPowers (u : R) (q r : ℕ) (hq : q.Prime) (hr : 0 < r)
    (hsize : r + 2 ≤ r * q) (hu : u ^ q = 1) (h : ∃ x : R, (q ^ r) • x = u - 1) (k : ℕ) :
    ∃ y : R, (q ^ k) • y = u - 1 := by
  obtain ⟨y, hy⟩ := primeOrder_congruence_depths u q r hq hr hsize hu h k
  refine ⟨(q ^ r) • y, ?_⟩
  rw [← mul_smul, ← pow_add, Nat.add_comm k r]
  exact hy

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrimeOrderCongruenceInflation
