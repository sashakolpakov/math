import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Localization.FractionRing

/-! # Transcendence Degree Transfer -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDegreeTransfer

/-!
# Transcendence degree under algebraic extensions

These results use mathlib's cardinal-valued transcendence degree and its
additivity theorem for faithful towers of domains. They apply in particular to
the integral extensions arising in Noether normalization. The prime-quotient
comparison uses the actual map induced on quotients, whose injectivity follows
from taking the inverse image of the prime ideal.
-/

universe u v w

section Towers

variable (k : Type u) (A B : Type v) [Field k]
  [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra k A] [Algebra k B] [Algebra A B]
  [IsScalarTower k A B] [FaithfulSMul A B]

/-- An algebraic faithful extension of domains preserves transcendence degree
over the common base field. -/
theorem trdeg_eq_of_isAlgebraic [Algebra.IsAlgebraic A B] :
    Algebra.trdeg k A = Algebra.trdeg k B := by
  simpa only [trdeg_eq_zero, add_zero] using (trdeg_add_eq k A (A := B))

/-- An integral faithful extension of domains preserves transcendence degree. -/
theorem trdeg_eq_of_isIntegral [Algebra.IsIntegral A B] :
    Algebra.trdeg k A = Algebra.trdeg k B :=
  trdeg_eq_of_isAlgebraic k A B

end Towers

section LiftedTowers

variable (k : Type u) (A : Type v) (B : Type w) [Field k]
  [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra k A] [Algebra k B] [Algebra A B]
  [IsScalarTower k A B] [FaithfulSMul A B]

/-- The universe-polymorphic form of algebraic transcendence-degree invariance. -/
theorem lift_trdeg_eq_of_isAlgebraic [Algebra.IsAlgebraic A B] :
    Cardinal.lift.{w} (Algebra.trdeg k A) =
      Cardinal.lift.{v} (Algebra.trdeg k B) := by
  simpa only [trdeg_eq_zero, Cardinal.lift_zero, add_zero] using
    (lift_trdeg_add_eq k A B)

/-- Integral invariance with the cardinal lifts required by distinct universes. -/
theorem lift_trdeg_eq_of_isIntegral [Algebra.IsIntegral A B] :
    Cardinal.lift.{w} (Algebra.trdeg k A) =
      Cardinal.lift.{v} (Algebra.trdeg k B) :=
  lift_trdeg_eq_of_isAlgebraic k A B

end LiftedTowers

section Fractions

variable (k : Type u) (A K : Type v) [Field k] [CommRing A] [IsDomain A]
  [Field K] [Algebra k A] [Algebra k K] [Algebra A K]
  [IsScalarTower k A K] [IsFractionRing A K]

/-- Passing from a domain to a fraction field does not alter its
transcendence degree over the base field. -/
theorem trdeg_eq_of_isFractionRing : Algebra.trdeg k A = Algebra.trdeg k K := by
  let : Algebra.IsAlgebraic A K :=
    IsLocalization.isAlgebraic K (nonZeroDivisors A)
  exact trdeg_eq_of_isAlgebraic k A K

/-- The standard fraction field has the same transcendence degree as its domain. -/
theorem trdeg_eq_fractionRing (k : Type u) (A : Type v) [Field k]
    [CommRing A] [IsDomain A] [Algebra k A] :
    Algebra.trdeg k A = Algebra.trdeg k (FractionRing A) :=
  trdeg_eq_of_isFractionRing k A (FractionRing A)

end Fractions

variable (k : Type u) {A B : Type v} [Field k]
  [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- A faithful integral algebra homomorphism identifies the transcendence
degrees of its source and target domains. -/
theorem trdeg_eq_of_injective_integral_algHom [IsDomain A] [IsDomain B]
    (f : A →ₐ[k] B) (hf : Function.Injective f) (hint : f.toRingHom.IsIntegral) :
    Algebra.trdeg k A = Algebra.trdeg k B := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower k A B := IsScalarTower.of_algHom f
  let : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr hf
  let : Algebra.IsIntegral A B := ⟨hint⟩
  exact trdeg_eq_of_isIntegral k A B

/-- Quotienting an integral algebra map by a prime and its inverse image
preserves transcendence degree. The original map need not be injective:
the induced map on these two quotients is injective by construction. -/
theorem trdeg_quotient_eq_of_integral_algHom (f : A →ₐ[k] B)
    (hint : f.toRingHom.IsIntegral) (P : Ideal B) [P.IsPrime] :
    Algebra.trdeg k (A ⧸ P.comap f) = Algebra.trdeg k (B ⧸ P) := by
  exact trdeg_eq_of_injective_integral_algHom k
    (Ideal.quotientMapₐ P f le_rfl) Ideal.quotientMap_injective hint.quotient

/-- The prime-quotient comparison for an integral tower over a field. -/
theorem trdeg_quotient_eq_of_isIntegral [Algebra A B] [IsScalarTower k A B]
    [Algebra.IsIntegral A B] (P : Ideal B) [P.IsPrime] :
    Algebra.trdeg k (A ⧸ P.comap (algebraMap A B)) =
      Algebra.trdeg k (B ⧸ P) := by
  exact trdeg_quotient_eq_of_integral_algHom k (IsScalarTower.toAlgHom k A B)
    Algebra.IsIntegral.isIntegral P

end OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDegreeTransfer
