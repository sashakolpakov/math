import OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSourcePrime
import OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveMinimalSupport
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Residual Minimal Source Prime -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ResidualMinimalSourcePrime.Constructions

noncomputable section

/-! A minimal residual component is a genuine minimal prime of the
source principal ideal; for a regular equation it has height one. -/

open OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSourcePrime.Constructions

set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] (P : Ideal R) (r : R)
  (p : PrimeSpectrum (R ⧸ Ideal.span {r}))
  (hp : p ∈ Module.support (R ⧸ Ideal.span {r}) (QuotSMulTop r (R ⧸ P)))
  (hm : p.asIdeal ∈ (Module.annihilator (R ⧸ Ideal.span {r}) (QuotSMulTop r (R ⧸ P))).minimalPrimes)

include hm

theorem sourcePrime_minimal :
    (ResidualSourcePrime.Constructions.sourcePrime R P r p hp).asIdeal ∈ (Ideal.span {algebraMap R (R ⧸ P) r}).minimalPrimes := by
  have hR := (SurjectiveMinimalSupport.Constructions.comap_mem_minimalPrimes_iff R (R ⧸ Ideal.span {r})
    (QuotSMulTop r (R ⧸ P)) Ideal.Quotient.mk_surjective p).mpr hm
  have ha := (QuotientEquationScalarChange.Constructions.algebraQuotientEquiv R (R ⧸ P) r).annihilator_eq
  rw [ha, ← ResidualSourcePrime.Constructions.sourcePrime_comap R P r p hp] at hR
  have hS := (SurjectiveMinimalSupport.Constructions.comap_mem_minimalPrimes_iff R (R ⧸ P)
    ((R ⧸ P) ⧸ Ideal.span {algebraMap R (R ⧸ P) r}) Ideal.Quotient.mk_surjective
    (ResidualSourcePrime.Constructions.sourcePrime R P r p hp)).mp hR
  rwa [Ideal.annihilator_quotient] at hS

theorem sourcePrime_height_one [IsNoetherianRing R]
    (hn : algebraMap R (R ⧸ P) r ∈ nonZeroDivisors (R ⧸ P)) :
    (ResidualSourcePrime.Constructions.sourcePrime R P r p hp).asIdeal.height = 1 := by
  have hmin := sourcePrime_minimal R P r p hp hm
  exact le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin)
    ((Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hn).trans (Ideal.height_mono hmin.le))

theorem minimal_mem_support :
    p ∈ Module.support (R ⧸ Ideal.span {r}) (QuotSMulTop r (R ⧸ P)) := by
  let : Module.Finite (R ⧸ Ideal.span {r}) (QuotSMulTop r (R ⧸ P)) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {r}) _
  exact Module.mem_support_iff_of_finite.mpr hm.le

def minimalSourcePrime : PrimeSpectrum (R ⧸ P) :=
  ResidualSourcePrime.Constructions.sourcePrime R P r p (minimal_mem_support R P r p hm)

theorem minimalSourcePrime_height_one [IsNoetherianRing R]
    (hn : algebraMap R (R ⧸ P) r ∈ nonZeroDivisors (R ⧸ P)) :
    (minimalSourcePrime R P r p hm).asIdeal.height = 1 :=
  sourcePrime_height_one R P r p (minimal_mem_support R P r p hm) hm hn

theorem localLength_eq_minimalSourcePrime_ord :
    LocalizedModuleLength.Constructions.localLength (R ⧸ Ideal.span {r}) (QuotSMulTop r (R ⧸ P)) p =
      Ring.ord (Localization.AtPrime (minimalSourcePrime R P r p hm).asIdeal)
        (algebraMap (R ⧸ P) (Localization.AtPrime (minimalSourcePrime R P r p hm).asIdeal)
          (algebraMap R (R ⧸ P) r)) :=
  ResidualSourcePrime.Constructions.localLength_eq_sourcePrime_ord R P r p (minimal_mem_support R P r p hm)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ResidualMinimalSourcePrime.Constructions
