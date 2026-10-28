import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.PrimePrincipal
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! # Factorial Two -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.FactorialTwo

noncomputable section

/-! A normal noetherian local domain with a residue-field projective
dimension bound of two is a unique factorization domain. -/

open _root_.CategoryTheory IsLocalRing

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsLocalRing R] [IsIntegrallyClosed R]

theorem dedekind_of_maximal_height_one (hm : (maximalIdeal R).height = 1) :
    IsDedekindDomain R := by
  let : Ring.DimensionLEOne R := ⟨by
    intro p hp hprime
    let := hprime
    have hheight : 1 ≤ p.height :=
      Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hp)
    have he : p = maximalIdeal R := p.eq_of_le_of_height_le
      (le_maximalIdeal hprime.ne_top) (by rw [hm]; exact hheight)
    exact he ▸ maximalIdeal.isMaximal R⟩
  exact
    { toIsDomain := inferInstance
      toIsDedekindRing :=
        { toIsNoetherian := inferInstance
          toDimensionLEOne := inferInstance
          toIsIntegralClosure := inferInstance } }

theorem factorial
    [HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) 2] :
    UniqueFactorizationMonoid R := by
  apply UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one
  intro p hp hheight
  by_cases he : p = maximalIdeal R
  · let : IsDedekindDomain R := dedekind_of_maximal_height_one R (he ▸ hheight)
    exact IsPrincipalIdealRing.principal p
  · exact PrimePrincipal.prime_principal R p he

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.FactorialTwo
