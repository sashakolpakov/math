import OAI.AlgebraicGeometry.CycleClass.Thom.QuotientEquationScalarChange
import OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveLocalLength
import OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedPrincipalOrder

/-! # Surjective Principal Order -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SurjectivePrincipalOrder.Constructions

noncomputable section

/-! A principal quotient of an algebra has its actual local order
as local multiplicity, also when measured over a surjecting base ring. -/

open OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength.Constructions

universe u v
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  (q : PrimeSpectrum S) (r : R) (hs : Function.Surjective (algebraMap R S))

include hs

theorem localLength_eq_ord :
    LocalizedModuleLength.Constructions.localLength R (QuotSMulTop r S) (PrimeSpectrum.comap (algebraMap R S) q) =
      Ring.ord (Localization.AtPrime q.asIdeal)
        (algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S r)) :=
  (LocalizedModuleLength.Constructions.localLength_equiv (QuotientEquationScalarChange.Constructions.algebraQuotientEquiv R S r)
    (PrimeSpectrum.comap (algebraMap R S) q)).trans
      ((SurjectiveLocalLength.Constructions.localLength_eq R S (S ⧸ Ideal.span {algebraMap R S r}) q hs).trans
        (LocalizedPrincipalOrder.Constructions.localLength_quotient_eq_ord S q (algebraMap R S r)))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SurjectivePrincipalOrder.Constructions
