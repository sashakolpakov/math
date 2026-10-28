import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.GoingDown

/-! # Regular Local -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.RegularLocal

noncomputable section

/-! Flat local unramified extensions of essentially finite type preserve
regular local rings: the maximal ideal is the extended maximal ideal,
and going down preserves its height. -/

open IsLocalRing

universe u v

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S]
  [IsRegularLocalRing R] [IsNoetherianRing S] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
  [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]

include R

theorem regular : IsRegularLocalRing S := by
  have hmap := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)
  have hheight : (maximalIdeal R).height ≤ (maximalIdeal S).height := by
    let : (maximalIdeal S).LiesOver (maximalIdeal R) :=
      ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm⟩
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
      (maximalIdeal R) (maximalIdeal S)]
    exact le_add_right le_rfl
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc
    ((maximalIdeal S).spanFinrank : WithBot ℕ∞) ≤ (maximalIdeal R).spanFinrank := by
      rw [← hmap]
      exact_mod_cast Ideal.spanFinrank_map_le_of_fg (algebraMap R S)
        (maximalIdeal R).fg_of_isNoetherianRing
    _ = ringKrullDim R := (isRegularLocalRing_iff R).mp inferInstance
    _ ≤ ringKrullDim S := by
      rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim]
      exact WithBot.coe_le_coe.mpr hheight

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.RegularLocal
