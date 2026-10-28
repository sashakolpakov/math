import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Group.Hom.End
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.BigOperators
import Lean.Elab.Tactic.Omega

/-! # Endomorphism Orbit Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EndomorphismOrbitPolynomial

noncomputable section

/-! A finite difference annihilating one additive orbit gives an explicit rational Newton polynomial for that orbit. -/
open _root_.Polynomial

theorem endomorphism_orbit_newton_of_apply_eq_zero {G : Type*} [AddCommGroup G]
    (T : AddMonoid.End G) (φ : G →+ ℤ) (x : G) (r : ℕ) (hr : ((T - 1) ^ r) x = 0) (n : ℕ) :
    φ ((T ^ n) x) = ∑ k ∈ Finset.range r, (n.choose k : ℤ) * φ (((T - 1) ^ k) x) := by
  let a := fun k => (n.choose k : ℤ) * φ (((T - 1) ^ k) x)
  have hn : φ ((T ^ n) x) = ∑ k ∈ Finset.range (n + 1), a k := by
    let ψ : AddMonoid.End G →+ ℤ :=
      { toFun := fun U => φ (U x)
        map_zero' := φ.map_zero
        map_add' := fun U V => φ.map_add (U x) (V x) }
    have hψ (U : AddMonoid.End G) : ψ U = φ (U x) := rfl
    have h := congrArg ψ ((Commute.one_right (T - 1)).add_pow n)
    rw [map_sum] at h
    simpa [hψ, a, nsmul_eq_mul] using h
  rw [hn]
  calc
    ∑ k ∈ Finset.range (n + 1), a k = ∑ k ∈ Finset.range (max (n + 1) r), a k := by
      apply Finset.sum_subset (Finset.range_mono (le_max_left _ _))
      intro k _ hk
      have hnk : n < k := by
        have := Finset.mem_range.not.mp hk
        omega
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

theorem exists_polynomial_of_endomorphism_difference_annihilates
    {G : Type*} [AddCommGroup G] (T : AddMonoid.End G) (φ : G →+ ℤ)
    (x : G) (r : ℕ) (hr : ((T - 1) ^ r) x = 0) :
    ∃ P : Polynomial ℚ, ∀ n : ℕ, P.eval (n : ℚ) = (φ ((T ^ n) x) : ℚ) :=
  ⟨endomorphismOrbitPolynomial T φ x r, endomorphismOrbitPolynomial_eval_of_apply_eq_zero T φ x r hr⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EndomorphismOrbitPolynomial
