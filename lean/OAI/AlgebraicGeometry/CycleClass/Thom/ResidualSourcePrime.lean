import OAI.AlgebraicGeometry.CycleClass.Thom.ResidualPrimeOrder
import OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveModuleSupport

/-! # Residual Source Prime -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSourcePrime.Constructions

noncomputable section

/-! Every actual residual support prime canonically determines a
prime of the source quotient with the same ambient inverse image. -/

open OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength.Constructions
open scoped Pointwise

set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] (P : Ideal R) (r : R)
  (p : PrimeSpectrum (R ⧸ Ideal.span {r}))
  (hp : p ∈ Module.support (R ⧸ Ideal.span {r}) (QuotSMulTop r (R ⧸ P)))

include hp

theorem sourceIdeal_le :
    P ≤ (PrimeSpectrum.comap (algebraMap R (R ⧸ Ideal.span {r})) p).asIdeal := by
  have hR := (SurjectiveModuleSupport.Constructions.comap_mem_support_iff R (R ⧸ Ideal.span {r})
    (QuotSMulTop r (R ⧸ P)) Ideal.Quotient.mk_surjective p).mpr hp
  have hS := Module.support_subset_of_surjective
    (r • (⊤ : Submodule R (R ⧸ P))).mkQ (Submodule.mkQ_surjective _) hR
  rwa [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] at hS

def sourcePrime : PrimeSpectrum (R ⧸ P) :=
  P.primeSpectrumQuotientOrderIsoZeroLocus.symm
    ⟨PrimeSpectrum.comap (algebraMap R (R ⧸ Ideal.span {r})) p, sourceIdeal_le R P r p hp⟩

theorem sourcePrime_comap :
    PrimeSpectrum.comap (algebraMap R (R ⧸ P)) (sourcePrime R P r p hp) =
      PrimeSpectrum.comap (algebraMap R (R ⧸ Ideal.span {r})) p :=
  congrArg Subtype.val (P.primeSpectrumQuotientOrderIsoZeroLocus.apply_symm_apply
    ⟨PrimeSpectrum.comap (algebraMap R (R ⧸ Ideal.span {r})) p, sourceIdeal_le R P r p hp⟩)

theorem localLength_eq_sourcePrime_ord :
    LocalizedModuleLength.Constructions.localLength (R ⧸ Ideal.span {r}) (QuotSMulTop r (R ⧸ P)) p =
      Ring.ord (Localization.AtPrime (sourcePrime R P r p hp).asIdeal)
        (algebraMap (R ⧸ P) (Localization.AtPrime (sourcePrime R P r p hp).asIdeal)
          (algebraMap R (R ⧸ P) r)) :=
  ResidualPrimeOrder.Constructions.localLength_eq_source_ord R P r p (sourcePrime R P r p hp)
    (sourcePrime_comap R P r p hp).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSourcePrime.Constructions
