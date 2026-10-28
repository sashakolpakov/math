import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Local Domain Components -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.LocalDomainComponents.Construction

noncomputable section

/-!
# Completion: distinct components cannot meet at a domain local ring
-/

open _root_.TopologicalSpace

variable (R : Type*) [CommRing R]

/-- A prime with domain localization contains at most one minimal prime. -/
theorem minimalPrime_unique_below_domain_localization (p : Ideal R) [p.IsPrime]
    [IsDomain (Localization.AtPrime p)] {a b : Ideal R}
    (ha : a ∈ minimalPrimes R) (hb : b ∈ minimalPrimes R) (hap : a ≤ p) (hbp : b ≤ p) :
    a = b := by
  let T := Localization.AtPrime p
  have h (c : Ideal R) (hc : c ∈ minimalPrimes R) (hcp : c ≤ p) :
      c = Ideal.comap (algebraMap R T) ⊥ := by
    have hd : Disjoint (p.primeCompl : Set R) c :=
      Set.disjoint_left.mpr fun r hr hc' => hr (hcp hc')
    have hu := IsLocalization.under_map_of_isPrime_disjoint p.primeCompl T hc.isPrime hd
    have hm : c.map (algebraMap R T) ∈ minimalPrimes T := by
      change c.map (algebraMap R T) ∈ (⊥ : Ideal T).minimalPrimes
      rw [← Ideal.map_bot (f := algebraMap R T), IsLocalization.minimalPrimes_map p.primeCompl T]
      simpa only [Set.mem_preimage, Ideal.under, hu] using hc
    rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at hm
    exact hu.symm.trans (congrArg (Ideal.comap (algebraMap R T)) hm)
  exact (h a ha hap).trans (h b hb hbp).symm

/-- Two irreducible components of an affine scheme meeting at a domain local ring coincide. -/
theorem affine_components_eq_of_domain_localization (x : PrimeSpectrum R)
    [IsDomain (Localization.AtPrime x.asIdeal)] {C D : Set (PrimeSpectrum R)}
    (hC : C ∈ irreducibleComponents (PrimeSpectrum R))
    (hD : D ∈ irreducibleComponents (PrimeSpectrum R)) (hxC : x ∈ C) (hxD : x ∈ D) :
    C = D := by
  have hc := isClosed_of_mem_irreducibleComponents C hC
  have hd := isClosed_of_mem_irreducibleComponents D hD
  have he : PrimeSpectrum.vanishingIdeal C = PrimeSpectrum.vanishingIdeal D :=
    minimalPrime_unique_below_domain_localization R x.asIdeal
      (PrimeSpectrum.vanishingIdeal_mem_minimalPrimes.mpr (by simpa only [hc.closure_eq] using hC))
      (PrimeSpectrum.vanishingIdeal_mem_minimalPrimes.mpr (by simpa only [hd.closure_eq] using hD))
      (fun r hr => (PrimeSpectrum.mem_vanishingIdeal _ _).mp hr x hxC)
      (fun r hr => (PrimeSpectrum.mem_vanishingIdeal _ _).mp hr x hxD)
  have := congrArg (fun I : Ideal R => PrimeSpectrum.zeroLocus (I : Set R)) he
  simpa only [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hc.closure_eq, hd.closure_eq]
    using this

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.LocalDomainComponents.Construction
