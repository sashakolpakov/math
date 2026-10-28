import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-! # Associated Prime Scalar Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AssociatedPrimeScalarInjectivity

/-! Multiplication on a finite module over a Noetherian ring is injective exactly when the scalar avoids its finite set of associated primes. This is a concrete finite family of scheme-point conditions, including embedded associated primes. -/
universe u v
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

theorem scalar_injective_iff_avoids_associatedPrimes (r : R) :
    Function.Injective (fun x : M => r • x) ↔
      ∀ P ∈ associatedPrimes R M, r ∉ P := by
  constructor
  · intro hinj P hP hr
    have hz : r ∈ ⋃ Q ∈ associatedPrimes R M, (Q : Set R) :=
      Set.mem_iUnion₂.mpr ⟨P, hP, hr⟩
    rw [biUnion_associatedPrimes_eq_zero_divisors R M] at hz
    obtain ⟨x, hx, hrx⟩ := hz
    exact hx (hinj (hrx.trans (smul_zero r).symm))
  · intro havoid x y hxy
    change r • x = r • y at hxy
    apply sub_eq_zero.mp
    by_contra hne
    have hz : r ∈ {a : R | ∃ z : M, z ≠ 0 ∧ a • z = 0} :=
      ⟨x - y, hne, by rw [smul_sub, hxy, sub_self]⟩
    rw [← biUnion_associatedPrimes_eq_zero_divisors R M] at hz
    obtain ⟨P, hP, hr⟩ := Set.mem_iUnion₂.mp hz
    exact havoid P hP hr

theorem exists_finite_prime_scalar_injectivity_test [Module.Finite R M] :
    ∃ (ι : Type u) (_ : Finite ι) (p : ι → PrimeSpectrum R),
      ∀ r : R, Function.Injective (fun x : M => r • x) ↔
        ∀ i, r ∉ (p i).asIdeal := by
  let ι := associatedPrimes R M
  have : Finite ι := (associatedPrimes.finite R M).to_subtype
  let p : ι → PrimeSpectrum R := fun P => ⟨P.val, P.property.isPrime⟩
  refine ⟨ι, inferInstance, p, fun r => ?_⟩
  rw [scalar_injective_iff_avoids_associatedPrimes]
  exact ⟨fun h i => h i.val i.property, fun h P hP => h ⟨P, hP⟩⟩

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AssociatedPrimeScalarInjectivity
