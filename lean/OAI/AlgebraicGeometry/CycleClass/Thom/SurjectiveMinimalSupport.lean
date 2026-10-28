import OAI.AlgebraicGeometry.CycleClass.Thom.MinimalSupportPrimes
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Surjective Minimal Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveMinimalSupport.Constructions

noncomputable section

/-! Minimal module-support primes correspond exactly under a
surjective scalar map, including their canonical finite enumerations. -/

open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.MinimalSupportPrimes.Constructions

universe u v w
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (hs : Function.Surjective (algebraMap R S))

include hs

theorem comap_mem_minimalPrimes_iff (q : PrimeSpectrum S) :
    (PrimeSpectrum.comap (algebraMap R S) q).asIdeal ∈ (Module.annihilator R M).minimalPrimes ↔
      q.asIdeal ∈ (Module.annihilator S M).minimalPrimes := by
  have ha : (Module.annihilator S M).comap (algebraMap R S) = Module.annihilator R M :=
    Module.comap_annihilator
  rw [← ha, Ideal.comap_minimalPrimes_eq_of_surjective hs]
  constructor
  · rintro ⟨I, hI, he⟩
    have hIq : I = q.asIdeal := Ideal.comap_injective_of_surjective (algebraMap R S) hs he
    exact hIq ▸ hI
  · intro hq
    exact ⟨q.asIdeal, hq, rfl⟩

theorem exists_comap_of_minimal (p : PrimeSpectrum R)
    (hp : p.asIdeal ∈ (Module.annihilator R M).minimalPrimes) :
    ∃ q : PrimeSpectrum S, q.asIdeal ∈ (Module.annihilator S M).minimalPrimes ∧
      PrimeSpectrum.comap (algebraMap R S) q = p := by
  have ha : (Module.annihilator S M).comap (algebraMap R S) = Module.annihilator R M :=
    Module.comap_annihilator
  rw [← ha, Ideal.comap_minimalPrimes_eq_of_surjective hs] at hp
  obtain ⟨I, hI, he⟩ := hp
  exact ⟨⟨I, hI.isPrime⟩, hI, PrimeSpectrum.ext he⟩

theorem minimalSupportPrimes_image [IsNoetherianRing R] [IsNoetherianRing S] :
    (MinimalSupportPrimes.Constructions.minimalSupportPrimes S M).image (PrimeSpectrum.comap (algebraMap R S)) =
      MinimalSupportPrimes.Constructions.minimalSupportPrimes R M := by
  ext p
  rw [Finset.mem_image, MinimalSupportPrimes.Constructions.mem_minimalSupportPrimes]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (comap_mem_minimalPrimes_iff R S M hs q).mpr ((MinimalSupportPrimes.Constructions.mem_minimalSupportPrimes S M q).mp hq)
  · intro hp
    obtain ⟨q, hq, he⟩ := exists_comap_of_minimal R S M hs p hp
    exact ⟨q, (MinimalSupportPrimes.Constructions.mem_minimalSupportPrimes S M q).mpr hq, he⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveMinimalSupport.Constructions
