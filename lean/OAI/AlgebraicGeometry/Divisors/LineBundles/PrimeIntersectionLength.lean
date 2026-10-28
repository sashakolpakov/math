import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalIntersectionLength
import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedPrimeFactor

/-! # Prime Intersection Length -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeIntersectionLength.BundleCycles

noncomputable section

/-!
# LineBundleCycles: prime-factor contributions are quotient lengths

On R/P, multiplication by an equation outside the prime P is injective.
Its cokernel is the actual quotient R/(P+(a)). Thus its finite Euler
contribution is exactly the local quotient length used by a divisor on
the prime support.
-/

variable {R : Type*} [CommRing R] (a : R) (J : Ideal R)

theorem quotientEquation_range :
    (MultiplicationSequence.BundleCycles.equationEndomorphism a (R ⧸ J)).range = Submodule.map J.mkQ (Ideal.span {a}) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨r, rfl⟩ := J.mkQ_surjective x
    exact ⟨a * r, (Ideal.span {a}).mul_mem_right r
      (Ideal.subset_span (Set.mem_singleton a)), rfl⟩
  · rintro _ ⟨r, hr, rfl⟩
    obtain ⟨x, rfl⟩ := (Ideal.mem_span_singleton.mp hr)
    exact ⟨J.mkQ x, rfl⟩

def primeEquationCokernelEquiv :
    MultiplicationSequence.BundleCycles.equationCokernel a (R ⧸ J) ≃ₗ[R] R ⧸ (J ⊔ Ideal.span {a}) :=
  (Submodule.quotEquivOfEq _ _ (quotientEquation_range a J)).trans
    (Submodule.quotientQuotientEquivQuotientSup J (Ideal.span {a}))

theorem primeEquation_injective [J.IsPrime] (ha : a ∉ J) :
    Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism a (R ⧸ J)) := by
  have hn : Ideal.Quotient.mk J a ≠ 0 := fun h => ha ((Ideal.Quotient.eq_zero_iff_mem).mp h)
  intro x y h
  exact mul_left_cancel₀ hn h

/-- The actual quotient-length contribution on the prime support. -/
def primeIntersectionQuotientLength : ℤ :=
  ((Module.length R (R ⧸ (J ⊔ Ideal.span {a}))).toNat : ℤ)

variable [IsNoetherianRing R]

theorem twoEquationEulerLength_prime (b : R) (hI : IsFiniteLength R (R ⧸ Ideal.span {a, b}))
    [J.IsPrime] (hb : b ∈ J) (ha : a ∉ J) :
    EquationFiniteLength.BundleCycles.twoEquationEulerLength a b hI (LocalizedPrimeFactor.BundleCycles.idealQuotient_annihilated J b hb) =
      primeIntersectionQuotientLength a J := by
  have hk : Module.length R (MultiplicationSequence.BundleCycles.equationKernel a (R ⧸ J)) = 0 := by
    change Module.length R (MultiplicationSequence.BundleCycles.equationEndomorphism a (R ⧸ J)).ker = 0
    rw [LinearMap.ker_eq_bot.mpr (primeEquation_injective a J ha), Module.length_bot]
  unfold EquationFiniteLength.BundleCycles.twoEquationEulerLength EquationEulerLength.BundleCycles.equationEulerLength primeIntersectionQuotientLength
  rw [hk, ENat.toNat_zero, Nat.cast_zero, sub_zero, (primeEquationCokernelEquiv a J).length_eq]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeIntersectionLength.BundleCycles
