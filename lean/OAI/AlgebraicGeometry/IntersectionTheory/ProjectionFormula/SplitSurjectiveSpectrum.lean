import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Split Surjective Spectrum -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SplitSurjectiveSpectrum

noncomputable section

/-! A prime containing the kernel of a split surjection is recovered
from its contraction along the section. This identifies diagonal primes
without choosing a noncanonical quotient-ring presentation. -/

universe u v

variable (R : Type u) (T : Type v) [CommRing R] [CommRing T]

theorem comap (μ : T →+* R) (s : R →+* T) (hs : μ.comp s = RingHom.id R)
    (p : PrimeSpectrum T) (hp : RingHom.ker μ ≤ p.asIdeal) :
    PrimeSpectrum.comap μ (PrimeSpectrum.comap s p) = p := by
  apply PrimeSpectrum.ext
  ext t
  change s (μ t) ∈ p.asIdeal ↔ t ∈ p.asIdeal
  have hd : t - s (μ t) ∈ p.asIdeal := hp (by
    change μ (t - s (μ t)) = 0
    have he : μ (s (μ t)) = μ t := RingHom.congr_fun hs (μ t)
    rw [map_sub, he, sub_self])
  constructor
  · intro ht
    simpa only [sub_add_cancel] using p.asIdeal.add_mem hd ht
  · intro ht
    simpa only [sub_sub_cancel] using p.asIdeal.sub_mem ht hd

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SplitSurjectiveSpectrum
