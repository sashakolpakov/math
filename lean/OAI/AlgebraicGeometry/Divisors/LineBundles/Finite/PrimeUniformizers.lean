import OAI.AlgebraicGeometry.Divisors.LineBundles.UniformizerPrimeAvoidance

/-! # Prime Uniformizers -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PrimeUniformizers.BundleCycles

noncomputable section

/-! # LineBundleCycles: simultaneous local uniformizers at a finite family of incomparable primes -/

variable {R ι : Type*} [CommRing R] [Finite ι]
    (P : ι → Ideal R) [∀ i, (P i).IsPrime]
    (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, IsLocalization.AtPrime (A i) (P i)] [∀ i, IsDomain (A i)]
    [∀ i, IsDiscreteValuationRing (A i)]
    (hne : Pairwise fun i j => ¬ P i ≤ P j)

include hne in
theorem exists_finitePrimeUniformizer (i : ι) :
    ∃ a : R, Irreducible (algebraMap R (A i) a) ∧ ∀ j, j ≠ i → a ∉ P j := by
  obtain ⟨a, ha, havoid⟩ := UniformizerPrimeAvoidance.BundleCycles.exists_uniformizer_avoiding_primes (P i) (A i)
    (fun j : {j : ι // j ≠ i} => P j.val) (fun j => inferInstance)
    (fun j => hne j.property.symm)
  exact ⟨a, ha, fun j hj => havoid ⟨j, hj⟩⟩

def finitePrimeUniformizer (i : ι) : R := (exists_finitePrimeUniformizer P A hne i).choose

theorem finitePrimeUniformizer_irreducible (i : ι) :
    Irreducible (algebraMap R (A i) (finitePrimeUniformizer P A hne i)) :=
  (exists_finitePrimeUniformizer P A hne i).choose_spec.1

theorem finitePrimeUniformizer_isUnit (i j : ι) (hji : j ≠ i) :
    IsUnit (algebraMap R (A j) (finitePrimeUniformizer P A hne i)) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (A j) (P j) _).mpr
  exact (exists_finitePrimeUniformizer P A hne i).choose_spec.2 j hji

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PrimeUniformizers.BundleCycles
