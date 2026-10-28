import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Data.Nat.Factorization.Basic

/-! # Padic Away Rationals -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicAwayRationals.TestTransport

noncomputable section

/-! A rational number integral at every prime other than q has a
denominator cleared by a power of q. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime]

theorem rational_integral_away_iff (r : ℚ) :
    (∀ (p : ℕ) [Fact p.Prime], p ≠ q → ‖(r : Padic p)‖ ≤ 1) ↔
      ∃ n : ℕ, ∃ z : ℤ, (z : ℚ) = (q : ℚ) ^ n * r := by
  constructor
  · intro h
    have hden : r.den.primeFactors ⊆ q.primeFactors := by
      intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      have hpq : p = q := by
        by_contra hpq
        let : Fact p.Prime := ⟨hp'⟩
        have hc : p.Coprime r.den := PadicInt.norm_natCast_eq_one_iff.mp
          (PadicInt.isUnit_iff.mp (PadicInt.isUnit_den r (h p hpq)))
        exact (hp'.coprime_iff_not_dvd.mp hc) hpd
      subst p
      exact Nat.mem_primeFactors.mpr ⟨Fact.out, dvd_refl _, (Fact.out : q.Prime).ne_zero⟩
    obtain ⟨n, hn⟩ := (Nat.exists_dvd_pow_iff r.den_ne_zero (Fact.out : q.Prime).ne_zero).mpr hden
    obtain ⟨k, hk⟩ := hn
    refine ⟨n, (k : ℤ) * r.num, ?_⟩
    have hpow : (q : ℚ) ^ n = (r.den : ℚ) * (k : ℚ) := by exact_mod_cast hk
    rw [hpow, Int.cast_mul, Int.cast_natCast, mul_right_comm, mul_comm (r.den : ℚ) r,
      Rat.mul_den_eq_num, mul_comm]
  · rintro ⟨n, z, hz⟩ p hp hpq
    have hcop : p.Coprime q := (Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr hpq
    have hqnorm : ‖(q : Padic p)‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr hcop
    have he : (z : Padic p) = (q : Padic p) ^ n * (r : Padic p) := by exact_mod_cast hz
    have hb := Padic.norm_int_le_one (p := p) z
    rw [he, norm_mul, norm_pow, hqnorm, one_pow, one_mul] at hb
    exact hb

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicAwayRationals.TestTransport
