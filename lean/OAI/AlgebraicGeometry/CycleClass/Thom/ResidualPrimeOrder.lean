import OAI.AlgebraicGeometry.CycleClass.Thom.SurjectivePrincipalOrder

/-! # Residual Prime Order -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ResidualPrimeOrder.Constructions

noncomputable section

/-! The residual multiplicity after cutting a prime quotient is the
actual local order on that source, at primes with the same ambient image. -/

open OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength.Constructions

universe u
variable (R : Type u) [CommRing R] (P : Ideal R) (r : R)
  (p : PrimeSpectrum (R ⧸ Ideal.span {r})) (q : PrimeSpectrum (R ⧸ P))

theorem localLength_eq_source_ord
    (hpq : PrimeSpectrum.comap (algebraMap R (R ⧸ Ideal.span {r})) p =
      PrimeSpectrum.comap (algebraMap R (R ⧸ P)) q) :
    LocalizedModuleLength.Constructions.localLength (R ⧸ Ideal.span {r}) (QuotSMulTop r (R ⧸ P)) p =
      Ring.ord (Localization.AtPrime q.asIdeal)
        (algebraMap (R ⧸ P) (Localization.AtPrime q.asIdeal) (algebraMap R (R ⧸ P) r)) := by
  rw [← SurjectiveLocalLength.Constructions.localLength_eq R (R ⧸ Ideal.span {r})
    (QuotSMulTop r (R ⧸ P)) p Ideal.Quotient.mk_surjective, hpq]
  exact SurjectivePrincipalOrder.Constructions.localLength_eq_ord R (R ⧸ P) q r Ideal.Quotient.mk_surjective

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ResidualPrimeOrder.Constructions
