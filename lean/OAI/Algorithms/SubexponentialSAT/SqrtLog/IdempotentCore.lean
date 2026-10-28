import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.LiftRing

namespace OAI.Algorithms

/-! The integral Newton operation for lifting an idempotent through a
nilpotent ideal. No division, characteristic hypothesis, or field structure
is used in the iteration. -/

namespace SubexponentialSAT.SqrtLog.Idempotent

variable {R S : Type*} [CommRing R] [CommRing S]

def newton (e : R) : R := 3 * e ^ 2 - 2 * e ^ 3

def iterate (e : R) : ℕ → R
  | 0 => e
  | n + 1 => newton (iterate e n)

theorem newton_error (e : R) :
    (newton e) ^ 2 - newton e =
      -(e ^ 2 - e) ^ 2 * (3 - 2 * e) * (1 + 2 * e) := by
  unfold newton
  ring

theorem newton_sub (e : R) :
    newton e - e = (1 - 2 * e) * (e ^ 2 - e) := by
  unfold newton
  ring

theorem newton_fixed {e : R} (he : e ^ 2 = e) : newton e = e := by
  apply sub_eq_zero.mp
  rw [newton_sub, he, sub_self, mul_zero]

theorem iterate_fixed {e : R} (he : e ^ 2 = e) (n : ℕ) : iterate e n = e := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [iterate, ih] using newton_fixed he

theorem map_newton (φ : R →+* S) (e : R) : φ (newton e) = newton (φ e) := by
  have h2 : φ (2 : R) = (2 : S) := by
    rw [show (2 : R) = 1 + 1 by ring, map_add, map_one]
    ring
  have h3 : φ (3 : R) = (3 : S) := by
    rw [show (3 : R) = 1 + 1 + 1 by ring, map_add, map_add, map_one]
    ring
  simp only [newton, map_sub, map_mul, map_pow, h2, h3]

theorem map_iterate (φ : R →+* S) (e : R) (n : ℕ) :
    φ (iterate e n) = iterate (φ e) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterate, map_newton, ih]

theorem iterate_residue (φ : R →+* S) {e : R}
    (he : (φ e) ^ 2 = φ e) (n : ℕ) : φ (iterate e n) = φ e := by
  rw [map_iterate, iterate_fixed he]

theorem error_dvd_power {q e : R} (h : q ∣ e ^ 2 - e) (n : ℕ) :
    q ^ (2 ^ n) ∣ (iterate e n) ^ 2 - iterate e n := by
  induction n with
  | zero => simpa [iterate] using h
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨-(c ^ 2) * (3 - 2 * iterate e n) * (1 + 2 * iterate e n), ?_⟩
      rw [iterate, newton_error, hc, Nat.pow_succ, pow_mul]
      ring

theorem iterate_idempotent {q e : R} {t n : ℕ}
    (h : q ∣ e ^ 2 - e) (hq : q ^ t = 0) (ht : t ≤ 2 ^ n) :
    (iterate e n) ^ 2 = iterate e n := by
  obtain ⟨c, hc⟩ := error_dvd_power h n
  have hpow : q ^ (2 ^ n) = 0 := by
    have hexp : 2 ^ n = t + (2 ^ n - t) := by omega
    rw [hexp, pow_add, hq, zero_mul]
  apply sub_eq_zero.mp
  rw [hc, hpow, zero_mul]

theorem idempotent_zero_of_dvd {q e : R} {t : ℕ}
    (he : e ^ 2 = e) (hq : q ^ t = 0) (hd : q ∣ e) : e = 0 := by
  obtain ⟨c, rfl⟩ := hd
  apply IsIdempotentElem.eq_zero_of_isNilpotent
  · simpa [IsIdempotentElem, pow_two] using he
  · exact ⟨t, by rw [mul_pow, hq, zero_mul]⟩

theorem idempotent_one_of_dvd {q e : R} {t : ℕ}
    (he : e ^ 2 = e) (hq : q ^ t = 0) (hd : q ∣ 1 - e) : e = 1 := by
  have hcomp : (1 - e) ^ 2 = 1 - e := by
    linear_combination he
  have hz := idempotent_zero_of_dvd hcomp hq hd
  exact (sub_eq_zero.mp hz).symm

theorem idempotent_zero_of_residue (φ : R →+* S) {q e : R} {t : ℕ}
    (hker : ∀ x, φ x = 0 → q ∣ x)
    (he : e ^ 2 = e) (hq : q ^ t = 0) (hres : φ e = 0) : e = 0 :=
  idempotent_zero_of_dvd he hq (hker e hres)

theorem idempotent_one_of_residue (φ : R →+* S) {q e : R} {t : ℕ}
    (hker : ∀ x, φ x = 0 → q ∣ x)
    (he : e ^ 2 = e) (hq : q ^ t = 0) (hres : φ e = 1) : e = 1 := by
  apply idempotent_one_of_dvd he hq
  apply hker
  simp [hres]

end SubexponentialSAT.SqrtLog.Idempotent

end OAI.Algorithms
