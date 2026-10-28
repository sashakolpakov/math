import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Support

/-! # Minimal Support Primes -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.MinimalSupportPrimes.Constructions

noncomputable section

/-! The finite set of genuine minimal primes of a module's annihilator. -/

open scoped Classical

universe u v
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  (M : Type v) [AddCommGroup M] [Module R M]

theorem finite_minimalSupportPrimes :
    {p : PrimeSpectrum R | p.asIdeal ∈ (Module.annihilator R M).minimalPrimes}.Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Module.annihilator R M)).preimage
    (fun _ _ _ _ h => PrimeSpectrum.ext h)

def minimalSupportPrimes : Finset (PrimeSpectrum R) := (finite_minimalSupportPrimes R M).toFinset

theorem mem_minimalSupportPrimes (p : PrimeSpectrum R) :
    p ∈ minimalSupportPrimes R M ↔ p.asIdeal ∈ (Module.annihilator R M).minimalPrimes :=
  Set.Finite.mem_toFinset _

end

end OAI.AlgebraicGeometry.CycleClass.Thom.MinimalSupportPrimes.Constructions
