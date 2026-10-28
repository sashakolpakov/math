import OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedPrimeLength
import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationQuotients
import Mathlib.RingTheory.OrderOfVanishing.Basic

/-! # Localized Principal Order -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedPrincipalOrder.Constructions

noncomputable section

/-! The local length of a principal quotient is exactly the native
order of its equation in the actual localized ring. -/

open OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedPrimeLength.Constructions

universe u
variable (R : Type u) [CommRing R] (p : PrimeSpectrum R) (r : R)

theorem localLength_quotient_eq_ord :
    LocalizedModuleLength.Constructions.localLength R (R ⧸ Ideal.span {r}) p =
      Ring.ord (Localization.AtPrime p.asIdeal) (algebraMap R (Localization.AtPrime p.asIdeal) r) := by
  rw [LocalizedModuleLength.Constructions.localLength, (LocalizedPrimeLength.Constructions.quotientEquiv R p (Ideal.span {r})).length_eq,
    Ideal.map_span, Set.image_singleton]
  rfl

theorem localLength_quotSMulTop_eq_ord :
    LocalizedModuleLength.Constructions.localLength R (QuotSMulTop r R) p =
      Ring.ord (Localization.AtPrime p.asIdeal) (algebraMap R (Localization.AtPrime p.asIdeal) r) :=
  (LocalizedModuleLength.Constructions.localLength_equiv
    (Submodule.quotEquivOfEq _ _ (Regular.EquationQuotients.Constructions.smul_top_eq_span R r)) p).trans
      (localLength_quotient_eq_ord R p r)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedPrincipalOrder.Constructions
