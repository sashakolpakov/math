import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.GroupWithZero.Associated

/-! # Prime Localization Units -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.PrimeLocalizationUnits

noncomputable section

/-! Units after inverting a prime element are scalar units times
integral powers of that element, expressed with explicit numerator and
denominator powers for use on projective chart overlaps. -/

universe u v
variable {R : Type u} [CommRing R] [IsDomain R]
variable {A : Type v} [CommRing A] [Algebra R A]

theorem primeLocalization_unit_powers (p : R) (hp : Prime p) [IsLocalization.Away p A]
    (z : Aˣ) : ∃ (c : Rˣ) (a b : ℕ),
      (z : A) * algebraMap R A p ^ b = algebraMap R A (c : R) * algebraMap R A p ^ a := by
  obtain ⟨b, r, hr⟩ := IsLocalization.Away.surj p (z : A)
  have hu : IsUnit (algebraMap R A r) := by
    rw [← hr]
    exact z.isUnit.mul ((IsLocalization.Away.algebraMap_isUnit p).pow b)
  obtain ⟨m, hm⟩ := (IsLocalization.Away.algebraMap_isUnit_iff (S := A) p).mp hu
  obtain ⟨a, _, ha⟩ := (dvd_prime_pow hp m).mp hm
  obtain ⟨c, hc⟩ := ha.symm
  refine ⟨c, a, b, ?_⟩
  rw [hr, ← hc, map_mul, map_pow, mul_comm]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.PrimeLocalizationUnits
