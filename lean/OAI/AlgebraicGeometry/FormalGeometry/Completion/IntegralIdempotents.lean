import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalRing.Basic

/-! # Integral Idempotents -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralIdempotents.Construction

/-! # Completion: idempotents in integral closures of local rings -/

open _root_.Polynomial

universe u v

variable (R : Type u) [CommRing R] {B : Type v} [CommRing B] [Algebra R B]

/-- An idempotent is integral over every base ring. -/
theorem idempotent_isIntegral {e : B} (he : IsIdempotentElem e) : IsIntegral R e := by
  refine ⟨X * (X - C (1 : R)), monic_X.mul (monic_X_sub_C _), ?_⟩
  simp [mul_sub, he.eq]

/-- A local ring has no nontrivial idempotents. -/
theorem local_idempotent_eq_zero_or_one [IsLocalRing R] {e : R} (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit h).mp he)
  · exact Or.inl (sub_eq_self.mp ((IsIdempotentElem.iff_eq_one_of_isUnit h).mp he.one_sub))

/-- If a local ring is integrally closed in an algebra, every idempotent of that algebra
is already zero or one. -/
theorem integralClosure_local_idempotent_eq_zero_or_one
    [IsLocalRing R] [IsIntegrallyClosedIn R B] {e : B} (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  obtain ⟨r, hr⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral (idempotent_isIntegral R he)
  have hri : IsIdempotentElem r := by
    apply (IsIntegralClosure.algebraMap_injective R R B)
    simpa only [map_mul, hr] using he.eq
  rcases local_idempotent_eq_zero_or_one R hri with h | h
  · left
    rw [← hr, h, map_zero]
  · right
    rw [← hr, h, map_one]

end OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralIdempotents.Construction
