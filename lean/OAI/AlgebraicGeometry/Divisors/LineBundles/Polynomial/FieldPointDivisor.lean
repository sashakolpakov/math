import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrincipalPrimeDivisor
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Field Point Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.FieldPointDivisor.BundleCycles

noncomputable section

/-! # LineBundleCycles: every nongeneric point of the affine line over a field is an actual principal divisor -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem polynomialFieldPoint_exists_principal (K : Type) [Field K]
    (p : Spec (.of (Polynomial K))) (hp : p.asIdeal ≠ ⊥) :
    ∃ a : Polynomial K, a ≠ 0 ∧
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (.of (Polynomial K)))
        (RegularDivisor.BundleCycles.globalFunctionFieldElement (Spec (.of (Polynomial K))) ((Scheme.ΓSpecIso (.of (Polynomial K))).inv a)) =
          Finsupp.single p 1 := by
  let : p.asIdeal.IsPrime := (show PrimeSpectrum (Polynomial K) from p).isPrime
  let a := Submodule.IsPrincipal.generator p.asIdeal
  have ha : a ≠ 0 := (Submodule.IsPrincipal.prime_generator_of_isPrime p.asIdeal hp).ne_zero
  have hspan : p.asIdeal = Ideal.span {a} := (Ideal.span_singleton_generator p.asIdeal).symm
  refine ⟨a, ha, ?_⟩
  change (RegularDivisor.BundleCycles.regularFunctionDivisor (Spec (.of (Polynomial K))) ((Scheme.ΓSpecIso (.of (Polynomial K))).inv a)).mapRange
    (fun n : ℤ => (n : ℚ)) Int.cast_zero = _
  rw [Affine.PrincipalPrimeDivisor.BundleCycles.affinePrincipalPrime_divisor p a hspan ha, Finsupp.mapRange_single, Int.cast_one]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.FieldPointDivisor.BundleCycles
