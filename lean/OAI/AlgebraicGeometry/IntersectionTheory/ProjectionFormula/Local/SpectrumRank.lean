import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceDimensionVanishing

/-! # Spectrum Rank -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SpectrumRank

noncomputable section

/-! A strictly decreasing dimension function on an ambient spectrum
gives a finite rank on an embedded local spectrum after subtracting
its value at the closed point. This rank bounds native quotient dimensions. -/

universe u v

open _root_.Order

theorem dimension_le_rank (R : Type u) [CommRing R]
    (ρ : PrimeSpectrum R → ℕ) (hρ : StrictAnti ρ) (p : PrimeSpectrum R) :
    ringKrullDim (R ⧸ p.asIdeal) ≤ (ρ p : WithBot ℕ∞) := by
  have h : coheight p ≤ (ρ p : ℕ∞) := by
    simpa only [coheight_toDual, height_nat] using
      coheight_le_coheight_apply_of_strictMono (fun q => OrderDual.toDual (ρ q)) hρ p
  rw [ringKrullDim_quotient]
  change krullDim (Set.Ici p) ≤ _
  rw [← coheight_eq_krullDim_Ici]
  exact WithBot.coe_le_coe.mpr h

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsLocalRing S]
  (f : R →+* S) (hf : StrictMono (PrimeSpectrum.comap f))
  (δ : PrimeSpectrum R → ℕ) (hδ : StrictAnti δ)

def rank (p : PrimeSpectrum S) : ℕ :=
  δ (PrimeSpectrum.comap f p) - δ (PrimeSpectrum.comap f (IsLocalRing.closedPoint S))

include hf hδ

theorem closed_le (p : PrimeSpectrum S) :
    δ (PrimeSpectrum.comap f (IsLocalRing.closedPoint S)) ≤ δ (PrimeSpectrum.comap f p) := by
  apply hδ.antitone
  apply hf.monotone
  exact IsLocalRing.le_maximalIdeal p.isPrime.ne_top

theorem strict : StrictAnti (rank R S f δ) := by
  intro p q hpq
  have h := hδ (hf hpq)
  have hc := closed_le R S f hf δ hδ q
  unfold rank
  omega

theorem dimension (p : PrimeSpectrum S) :
    ringKrullDim (S ⧸ p.asIdeal) ≤
      (δ (PrimeSpectrum.comap f p) - δ (PrimeSpectrum.comap f (IsLocalRing.closedPoint S)) : ℕ) :=
  dimension_le_rank S (rank R S f δ) (strict R S f hf δ hδ) p

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SpectrumRank
