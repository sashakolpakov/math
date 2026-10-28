import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! # Weierstrass Prime Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.WeierstrassPrimeIs.Construction.WeierstrassPrime

/-!
# Prime factors under Weierstrass preparation

The quotient comparison in Weierstrass division transports primeness between
a distinguished polynomial and its power series. Conversely, a divisor of
a distinguished polynomial which becomes a power-series unit was already a
polynomial unit. These facts give prime factorization for series with a
nonzero reduction over a complete local factorial ring.
-/

open scoped _root_.Polynomial

variable {R : Type*} [CommRing R]

theorem prime_coe_iff {I : Ideal R} [IsAdicComplete I R]
    {f : R[X]} (hf : f.IsDistinguishedAt I) (h0 : f ≠ 0) :
    Prime (f : PowerSeries R) ↔ Prime f := by
  have h0' : (f : PowerSeries R) ≠ 0 := by simpa using h0
  rw [← Ideal.span_singleton_prime h0', ← Ideal.span_singleton_prime h0,
    ← Ideal.Quotient.isDomain_iff_prime, ← Ideal.Quotient.isDomain_iff_prime]
  exact hf.algEquivQuotient.toRingEquiv.toMulEquiv.isDomain_iff.symm

variable [IsDomain R] [IsLocalRing R]

theorem isUnit_of_dvd_distinguished {f g : R[X]}
    (hf : f.IsDistinguishedAt (IsLocalRing.maximalIdeal R))
    (hg : g ∣ f) (hu : IsUnit (g : PowerSeries R)) : IsUnit g := by
  let ρ := IsLocalRing.residue R
  have hg0 : IsUnit (g.coeff 0) := by
    simpa using PowerSeries.isUnit_iff_constantCoeff.mp hu
  have hmap : g.map ρ ∣ Polynomial.X ^ f.natDegree := by
    have he : f.map ρ = Polynomial.X ^ f.natDegree := hf.map_eq_X_pow
    rw [← he]
    exact Polynomial.map_dvd ρ hg
  obtain ⟨i, _, hi⟩ := (dvd_prime_pow (Polynomial.prime_X (R := IsLocalRing.ResidueField R))
    f.natDegree).mp hmap
  have hi0 : i = 0 := by
    by_contra h
    have hx : Polynomial.X ∣ g.map ρ := by
      exact hi.dvd_iff_dvd_right.mpr (dvd_pow_self _ h)
    have hz : ρ (g.coeff 0) = 0 := by
      simpa using Polynomial.X_dvd_iff.mp hx
    exact (hg0.map ρ).ne_zero hz
  have hunit : IsUnit (g.map ρ) := by
    rw [hi0, pow_zero] at hi
    exact hi.isUnit_iff.mpr isUnit_one
  exact Polynomial.isUnit_of_isUnit_leadingCoeff_of_isUnit_map ρ
    (hf.monic.isUnit_leadingCoeff_of_dvd hg) hunit

theorem irreducible_of_coe {f : R[X]}
    (hf : f.IsDistinguishedAt (IsLocalRing.maximalIdeal R))
    (hi : Irreducible (f : PowerSeries R)) : Irreducible f := by
  refine ⟨fun hu => hi.not_isUnit (hu.map Polynomial.coeToPowerSeries.ringHom), ?_⟩
  intro a b h
  have h' : (f : PowerSeries R) = (a : PowerSeries R) * (b : PowerSeries R) := by
    simpa using congrArg (fun k : R[X] => (k : PowerSeries R)) h
  rcases hi.isUnit_or_isUnit h' with ha | hb
  · exact Or.inl (isUnit_of_dvd_distinguished hf ⟨b, h⟩ ha)
  · exact Or.inr (isUnit_of_dvd_distinguished hf ⟨a, h.trans (mul_comm _ _)⟩ hb)

variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
variable [UniqueFactorizationMonoid R]

theorem prime_of_irreducible_of_reduction_ne_zero {f : PowerSeries R}
    (hf : f.map (IsLocalRing.residue R) ≠ 0) (hi : Irreducible f) : Prime f := by
  obtain ⟨g, u, h⟩ := f.exists_isWeierstrassFactorization hf
  have ha : Associated f (g : PowerSeries R) := by
    rw [h.eq_mul]
    exact associated_mul_unit_left _ _ h.isUnit
  have hg : Irreducible g := irreducible_of_coe h.isDistinguishedAt
    (ha.irreducible_iff.mp hi)
  exact ha.prime_iff.mpr ((prime_coe_iff h.isDistinguishedAt hg.ne_zero).mpr hg.prime)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.WeierstrassPrimeIs.Construction.WeierstrassPrime
