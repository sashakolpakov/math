import OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-! # Localized Prime Length -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedPrimeLength.Constructions

noncomputable section

/-! The localization of an actual prime quotient at its own prime
is the residue module and therefore has length one. -/

open OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength.Constructions

universe u
variable (R : Type u) [CommRing R] (p : PrimeSpectrum R)

theorem localizedIdeal_eq_map (I : Ideal R) :
    I.localized' (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl
      (Algebra.linearMap R (Localization.AtPrime p.asIdeal)) =
      I.map (algebraMap R (Localization.AtPrime p.asIdeal)) := by
  rw [Submodule.localized'_eq_span, Ideal.map, Ideal.span, Algebra.coe_linearMap]

def quotientEquiv (I : Ideal R) :
    LocalizedModule p.asIdeal.primeCompl (R ⧸ I) ≃ₗ[Localization.AtPrime p.asIdeal]
      (Localization.AtPrime p.asIdeal) ⧸ I.map (algebraMap R (Localization.AtPrime p.asIdeal)) :=
  ((IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (R ⧸ I))
    (I.toLocalizedQuotient' (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl
      (Algebra.linearMap R (Localization.AtPrime p.asIdeal)))).extendScalarsOfIsLocalization
        p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)).trans
          (Submodule.quotEquivOfEq _ _ (localizedIdeal_eq_map R p I))

theorem localLength_self : LocalizedModuleLength.Constructions.localLength R (R ⧸ p.asIdeal) p = 1 := by
  rw [LocalizedModuleLength.Constructions.localLength, (quotientEquiv R p p.asIdeal).length_eq,
    Localization.AtPrime.map_eq_maximalIdeal]
  let : IsSimpleModule (Localization.AtPrime p.asIdeal)
      ((Localization.AtPrime p.asIdeal) ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) :=
    isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
  exact Module.length_eq_one _ _

theorem localLength_prime_of_not_le (q : PrimeSpectrum R) (h : ¬ q.asIdeal ≤ p.asIdeal) :
    LocalizedModuleLength.Constructions.localLength R (R ⧸ q.asIdeal) p = 0 := by
  apply LocalizedModuleLength.Constructions.localLength_eq_zero
  rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
  exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedPrimeLength.Constructions
