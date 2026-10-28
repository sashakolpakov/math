import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceVanishing
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Sequence Dimension Vanishing -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceDimensionVanishing

noncomputable section

/-! The support-rank vanishing theorem specialized to the actual Krull
dimension of prime quotients in a Noetherian local ring. -/

universe u

open _root_.Order RingTheory.Sequence OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceModule

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

def rank (p : PrimeSpectrum R) : ℕ := (coheight p).toNat

theorem rank_coe (p : PrimeSpectrum R) : (rank R p : ℕ∞) = coheight p :=
  ENat.natCast_toNat (coheight_lt_top p).ne

theorem rank_strict : StrictAnti (rank R) := by
  intro p q hpq
  have h := coheight_strictAnti hpq (coheight_lt_top q)
  rw [← rank_coe R p, ← rank_coe R q] at h
  exact_mod_cast h

theorem rank_dimension (p : PrimeSpectrum R) :
    (rank R p : WithBot ℕ∞) = ringKrullDim (R ⧸ p.asIdeal) := by
  rw [ringKrullDim_quotient]
  change (rank R p : WithBot ℕ∞) = krullDim (Set.Ici p)
  rw [← coheight_eq_krullDim_Ici]
  exact congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) (rank_coe R p)

theorem euler_zero (rs : List R) (hreg : IsRegular R rs)
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hdim : ∀ p ∈ Module.support R M, ringKrullDim (R ⧸ p.asIdeal) < rs.length)
    (hiso : Module.support R M ∩ Module.support R (SequenceModule.quotient R rs) ⊆ {IsLocalRing.closedPoint R}) :
    Tor.Euler.euler R M (SequenceModule.quotient R rs) rs.length = 0 := by
  apply SequenceVanishing.euler_zero R rs hreg (rank R) (rank_strict R) M _ hiso
  intro p hp
  have h := hdim p hp
  rw [← rank_dimension R p] at h
  exact_mod_cast h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceDimensionVanishing
