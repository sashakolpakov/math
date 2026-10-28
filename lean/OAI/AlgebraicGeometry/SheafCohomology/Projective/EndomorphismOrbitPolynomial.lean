import OAI.AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitDifference
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Nilpotent.Defs
import Lean.Elab.Tactic.Omega

/-! # Endomorphism Orbit Polynomial -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitPolynomial

noncomputable section

/-! A nilpotent tensor difference gives an actual rational polynomial for every additive index orbit. -/

open _root_.Polynomial

theorem endomorphism_orbit_newton_of_apply_eq_zero {G : Type*} [AddCommGroup G] (T : AddMonoid.End G)
    (φ : G →+ ℤ) (x : G) (r : ℕ) (hr : ((T - 1) ^ r) x = 0) (n : ℕ) :
    φ ((T ^ n) x) = ∑ k ∈ Finset.range r, (n.choose k : ℤ) * φ (((T - 1) ^ k) x) := by
  let a := fun k => (n.choose k : ℤ) * φ (((T - 1) ^ k) x)
  have hn : φ ((T ^ n) x) = ∑ k ∈ Finset.range (n + 1), a k := by
    have h := shift_eq_sum_fwdDiff_iter 1 (fun k : ℕ => φ ((T ^ k) x)) n 0
    simpa only [nsmul_eq_mul, Nat.cast_id, mul_one, zero_add, EndomorphismOrbitDifference.endomorphism_orbit_fwdDiff,
      pow_zero, AddMonoid.End.one_apply, a] using h
  rw [hn]
  calc
    ∑ k ∈ Finset.range (n + 1), a k = ∑ k ∈ Finset.range (max (n + 1) r), a k := by
      apply Finset.sum_subset (Finset.range_mono (le_max_left _ _))
      intro k _ hk
      have hnk : n < k := by have := Finset.mem_range.not.mp hk; omega
      simp only [a, Nat.choose_eq_zero_of_lt hnk, Nat.cast_zero, zero_mul]
    _ = ∑ k ∈ Finset.range r, a k := by
      symm
      apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
      intro k _ hk
      have hrk : r ≤ k := Nat.not_lt.mp (Finset.mem_range.not.mp hk)
      have hkx : ((T - 1) ^ k) x = 0 := by
        rw [← Nat.sub_add_cancel hrk, pow_add]
        change ((T - 1) ^ (k - r)) (((T - 1) ^ r) x) = 0
        rw [hr, map_zero]
      dsimp only [a]
      rw [hkx, map_zero, mul_zero]

theorem endomorphism_orbit_newton {G : Type*} [AddCommGroup G] (T : AddMonoid.End G)
    (φ : G →+ ℤ) (x : G) (r : ℕ) (hr : (T - 1) ^ r = 0) (n : ℕ) :
    φ ((T ^ n) x) = ∑ k ∈ Finset.range r, (n.choose k : ℤ) * φ (((T - 1) ^ k) x) :=
  endomorphism_orbit_newton_of_apply_eq_zero T φ x r (by rw [hr]; rfl) n

def endomorphismOrbitPolynomial {G : Type*} [AddCommGroup G] (T : AddMonoid.End G)
    (φ : G →+ ℤ) (x : G) (r : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range r,
    C ((φ (((T - 1) ^ k) x) : ℚ) / (Nat.factorial k : ℚ)) * descPochhammer ℚ k

theorem endomorphismOrbitPolynomial_eval_of_apply_eq_zero {G : Type*} [AddCommGroup G]
    (T : AddMonoid.End G) (φ : G →+ ℤ) (x : G) (r : ℕ) (hr : ((T - 1) ^ r) x = 0) (n : ℕ) :
    (endomorphismOrbitPolynomial T φ x r).eval (n : ℚ) = (φ ((T ^ n) x) : ℚ) := by
  rw [endomorphism_orbit_newton_of_apply_eq_zero T φ x r hr n]
  simp only [endomorphismOrbitPolynomial, eval_finsetSum, eval_mul, eval_C,
    Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.cast_choose_eq_descPochhammer_div]
  ring

theorem endomorphismOrbitPolynomial_eval {G : Type*} [AddCommGroup G] (T : AddMonoid.End G)
    (φ : G →+ ℤ) (x : G) (r : ℕ) (hr : (T - 1) ^ r = 0) (n : ℕ) :
    (endomorphismOrbitPolynomial T φ x r).eval (n : ℚ) = (φ ((T ^ n) x) : ℚ) :=
  endomorphismOrbitPolynomial_eval_of_apply_eq_zero T φ x r (by rw [hr]; rfl) n

theorem endomorphismOrbitPolynomial_natDegree_le {G : Type*} [AddCommGroup G]
    (T : AddMonoid.End G) (φ : G →+ ℤ) (x : G) (r : ℕ) :
    (endomorphismOrbitPolynomial T φ x r).natDegree ≤ r - 1 := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  apply (natDegree_C_mul_le _ _).trans
  rw [descPochhammer_natDegree]
  have := Finset.mem_range.mp hk
  omega

theorem exists_polynomial_of_nilpotent_endomorphism_difference
    {G : Type*} [AddCommGroup G] (T : AddMonoid.End G) (φ : G →+ ℤ)
    (hT : IsNilpotent (T - 1)) (x : G) :
    ∃ P : Polynomial ℚ, ∀ n : ℕ, P.eval (n : ℚ) = (φ ((T ^ n) x) : ℚ) := by
  obtain ⟨r, hr⟩ := hT
  exact ⟨endomorphismOrbitPolynomial T φ x r,
    endomorphismOrbitPolynomial_eval T φ x r hr⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitPolynomial
