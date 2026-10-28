import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Noetherian.Defs

/-! # Ideal Neighborhood -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IdealNeighborhood.Constructions

noncomputable section

/-!
# DegreeTwo: descend a finitely generated ideal inclusion to one neighborhood

A localization inclusion for a finitely generated ideal has a single
common denominator. This will identify the actual parameter's zero locus
with its prime divisor on a genuine principal neighborhood.
-/

/-- One element of the localization monoid clears the entire finitely
generated ideal inclusion, not just each generator separately. -/
theorem exists_common_ideal_denominator {R : Type*} [CommRing R]
    (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]
    (I J : Ideal R) (hJ : J.FG)
    (hJI : J.map (algebraMap R S) ≤ I.map (algebraMap R S)) :
    ∃ b : M, ∀ r ∈ J, b.val * r ∈ I := by
  classical
  obtain ⟨s, hs⟩ := hJ
  have hgen : ∀ r : s, ∃ b : M, b.val * r.val ∈ I := by
    intro r
    have hrJ : r.val ∈ J := by
      rw [← hs]
      exact Ideal.subset_span r.property
    obtain ⟨b, hb, hbr⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M S I r.val).mp
      (hJI (Ideal.mem_map_of_mem (algebraMap R S) hrJ))
    exact ⟨⟨b, hb⟩, hbr⟩
  choose den hden using hgen
  let b : R := ∏ r : s, (den r).val
  have hb : b ∈ M := M.prod_mem (fun r _ => (den r).property)
  have hbs : ∀ r ∈ s, b * r ∈ I := by
    intro r hr
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun t : s => (den t).val)
      (Finset.mem_univ (⟨r, hr⟩ : s))
    change b = (den ⟨r, hr⟩).val * c at hc
    rw [hc]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using I.mul_mem_left c (hden ⟨r, hr⟩)
  have hcolon : J ≤ I.colon ({b} : Set R) := by
    rw [← hs, Ideal.span_le]
    intro r hr
    apply Submodule.mem_colon_singleton.mpr
    change r * b ∈ I
    rw [mul_comm]
    exact hbs r hr
  refine ⟨⟨b, hb⟩, ?_⟩
  intro r hr
  have h := Submodule.mem_colon_singleton.mp (hcolon hr)
  change r * b ∈ I at h
  rwa [mul_comm] at h

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IdealNeighborhood.Constructions
