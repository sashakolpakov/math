import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SpectrumRank
import OAI.AlgebraicGeometry.Foundations.Scheme.StrictTranscendenceDrop

/-! # Spectrum Rank -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SpectrumRank

noncomputable section

/-! Transcendence dimensions on a finite-type affine spectrum provide
the actual decreasing rank used to bound dimensions on embedded local
spectra. -/

universe u

variable (K A : Type u) [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]

def dimension (p : PrimeSpectrum A) : ℕ := (Algebra.trdeg K (A ⧸ p.asIdeal)).toNat

theorem strict : StrictAnti (dimension K A) := by
  intro p q hpq
  exact Foundations.Scheme.StrictTranscendenceDrop.trdeg_toNat_quotient_lt_of_prime_lt (k := K) hpq

theorem local_bound (S : Type u) [CommRing S] [IsLocalRing S]
    (f : A →+* S) (hf : StrictMono (PrimeSpectrum.comap f))
    (p : PrimeSpectrum S) (d : ℕ)
    (hp : dimension K A (PrimeSpectrum.comap f p) <
      d + dimension K A (PrimeSpectrum.comap f (IsLocalRing.closedPoint S))) :
    ringKrullDim (S ⧸ p.asIdeal) < d := by
  have h := Local.SpectrumRank.dimension A S f hf (dimension K A) (strict K A) p
  have hc := Local.SpectrumRank.closed_le A S f hf (dimension K A) (strict K A) p
  have hn : dimension K A (PrimeSpectrum.comap f p) -
      dimension K A (PrimeSpectrum.comap f (IsLocalRing.closedPoint S)) < d := by omega
  exact h.trans_lt (by exact_mod_cast hn)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SpectrumRank
