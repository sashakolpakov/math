import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.MaxDomain
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Zero

/-! # Local One -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.LocalOne

noncomputable section

/-! A positive-dimensional noetherian local ring with principal maximal
ideal is a domain. In particular every one-dimensional regular local
ring is a discrete valuation ring. -/

open IsLocalRing

universe u

variable (R : Type u) [CommRing R]

theorem domain_of_principal [IsNoetherianRing R] [IsLocalRing R]
    (hm : (maximalIdeal R).IsPrincipal)
    (hd : 0 < ringKrullDim R) : IsDomain R := by
  obtain ⟨r, hr⟩ := hm.principal
  apply Principal.MaxDomain.domain R r hr
  intro hnil
  have hprime (p : Ideal R) (hp : p.IsPrime) : p = maximalIdeal R := by
    let := hp
    apply le_antisymm (le_maximalIdeal hp.ne_top)
    rw [hr]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (nilradical_le_prime p hnil))
  let : Ring.KrullDimLE 0 R := .mk₀ (fun p hp => hprime p hp ▸ maximalIdeal.isMaximal R)
  have hz : ringKrullDim R = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  exact (ne_of_gt hd) hz

theorem domain [IsRegularLocalRing R] (hd : ringKrullDim R = 1) : IsDomain R := by
  have hspan : (maximalIdeal R).spanFinrank = 1 := by
    have h := ((isRegularLocalRing_iff R).mp inferInstance).trans hd
    exact_mod_cast h
  exact domain_of_principal R ((Submodule.spanFinrank_eq_one_iff _).mp hspan).1
    (hd ▸ by norm_num)

theorem dvr [IsRegularLocalRing R] [IsDomain R] (hd : ringKrullDim R = 1) :
    IsDiscreteValuationRing R := by
  have hspan : (maximalIdeal R).spanFinrank = 1 := by
    have h := ((isRegularLocalRing_iff R).mp inferInstance).trans hd
    exact_mod_cast h
  have hm := ((Submodule.spanFinrank_eq_one_iff _).mp hspan).1
  apply ((IsDiscreteValuationRing.TFAE R ?_).out 5 1 rfl rfl).mp hm
  intro hf
  let := hf.toField
  have hz : ringKrullDim R = 0 := by simp
  rw [hd] at hz
  norm_num at hz

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.LocalOne
