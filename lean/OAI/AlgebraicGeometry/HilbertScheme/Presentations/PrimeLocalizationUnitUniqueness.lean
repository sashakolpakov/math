import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PrimeLocalizationUnits
import Mathlib.Algebra.GroupWithZero.Divisibility

/-! # Prime Localization Unit Uniqueness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.PrimeLocalizationUnitUniqueness

noncomputable section

/-! A unit's scalar and integral exponent after prime localization
are unique, independently of a numerator-denominator presentation. -/

universe u v
variable {R : Type u} [CommRing R] [IsDomain R]
variable {A : Type v} [CommRing A] [Algebra R A]
variable (p : R) (hp : Prime p) [IsLocalization.Away p A]

include p hp in
theorem primeLocalization_injective : Function.Injective (algebraMap R A) := by
  apply IsLocalization.injective (M := Submonoid.powers p)
  rintro r ⟨m, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero m hp.ne_zero)

include hp in
theorem primeLocalization_scalar_power_unique (c d : Rˣ) (a b : ℕ)
    (h : algebraMap R A (c : R) * algebraMap R A p ^ a =
      algebraMap R A (d : R) * algebraMap R A p ^ b) : c = d ∧ a = b := by
  have he : (c : R) * p ^ a = (d : R) * p ^ b :=
    primeLocalization_injective (A := A) p hp (by simpa only [map_mul, map_pow] using h)
  have ha : Associated (p ^ a) (p ^ b) :=
    (associated_unit_mul_right (p ^ a) (c : R) c.isUnit).trans
      (he.symm ▸ associated_unit_mul_left (p ^ b) (d : R) d.isUnit)
  have hab : a = b := Nat.le_antisymm
    ((pow_dvd_pow_iff hp.ne_zero hp.not_isUnit).mp ha.dvd)
    ((pow_dvd_pow_iff hp.ne_zero hp.not_isUnit).mp ha.symm.dvd)
  subst b
  exact ⟨Units.ext (mul_right_cancel₀ (pow_ne_zero a hp.ne_zero) he), rfl⟩

include hp in
theorem primeLocalization_unit_exponent_unique (z : Aˣ) (c d : Rˣ) (a b k l : ℕ)
    (h : (z : A) * algebraMap R A p ^ b = algebraMap R A (c : R) * algebraMap R A p ^ a)
    (h' : (z : A) * algebraMap R A p ^ l = algebraMap R A (d : R) * algebraMap R A p ^ k) :
    c = d ∧ (a : ℤ) - b = (k : ℤ) - l := by
  have he : algebraMap R A (c : R) * algebraMap R A p ^ (a + l) =
      algebraMap R A (d : R) * algebraMap R A p ^ (k + b) := by
    calc
      _ = ((z : A) * algebraMap R A p ^ b) * algebraMap R A p ^ l := by
        rw [h, pow_add, mul_assoc]
      _ = ((z : A) * algebraMap R A p ^ l) * algebraMap R A p ^ b := mul_right_comm _ _ _
      _ = _ := by rw [h', pow_add, mul_assoc]
  obtain ⟨hc, he⟩ := primeLocalization_scalar_power_unique p hp c d (a + l) (k + b) he
  exact ⟨hc, by omega⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.PrimeLocalizationUnitUniqueness
