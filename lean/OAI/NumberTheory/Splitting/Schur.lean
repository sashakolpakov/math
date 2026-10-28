import Mathlib

/-! # Schur -/

namespace OAI.NumberTheory.Splitting.Schur.SplitPrimesConstruction

/-! Elementary prime divisors of polynomial values, for the SplitPrimes proof. -/

open _root_.Polynomial

/-- A nonconstant integral polynomial has a nonzero value divisible by a
prime avoiding any prescribed nonzero integer. -/
theorem exists_prime_dvd_eval_avoiding
    (f : ℤ[X]) (hf : f.natDegree ≠ 0) (m : ℤ) (hm : m ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ m ∧
      ∃ z : ℤ, f.eval z ≠ 0 ∧ (p : ℤ) ∣ f.eval z := by
  classical
  have := f.tendstoCofinite_of_natDegree_ne_zero hf
  obtain ⟨a, ha⟩ :=
    (Filter.TendstoCofinite.finite_preimage f.eval (Set.finite_singleton 0)).exists_notMem
  change f.eval a ≠ 0 at ha
  let u : ℤ → ℤ := fun x ↦ a + f.eval a * m * x
  have hu : Function.Injective u := by
    intro x y h
    exact mul_left_cancel₀ (mul_ne_zero ha hm) (add_left_cancel h)
  have := Filter.tendstoCofinite_of_injective hu
  have := Filter.TendstoCofinite.comp u f.eval
  have hfinite : ({0, f.eval a, -f.eval a} : Set ℤ).Finite := by simp
  obtain ⟨x, hx⟩ :=
    (Filter.TendstoCofinite.finite_preimage (f.eval ∘ u) hfinite).exists_notMem
  have hvals : f.eval (u x) ≠ 0 ∧ f.eval (u x) ≠ f.eval a ∧
      f.eval (u x) ≠ -f.eval a := by simpa using hx
  obtain ⟨t, ht⟩ := sub_dvd_eval_sub (u x) a f
  have heq : f.eval (u x) = f.eval a * (1 + m * x * t) := by
    dsimp [u] at ht
    nlinarith [ht]
  have hk : (1 + m * x * t).natAbs ≠ 1 := by
    intro h
    rcases Int.natAbs_eq_iff.mp h with h | h
    · exact hvals.2.1 (by simpa [h] using heq)
    · exact hvals.2.2 (by simpa [h] using heq)
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk
  have hpk' : (p : ℤ) ∣ 1 + m * x * t := Int.natCast_dvd.mpr hpk
  refine ⟨p, hp, ?_, u x, hvals.1, ?_⟩
  · intro hpm
    have hone : (p : ℤ) ∣ 1 := by
      simpa using dvd_sub hpk' (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpm x) t)
    have : p ∣ 1 := by exact_mod_cast hone
    exact hp.not_dvd_one this
  · rw [heq]
    exact dvd_mul_of_dvd_right hpk' _

end OAI.NumberTheory.Splitting.Schur.SplitPrimesConstruction
