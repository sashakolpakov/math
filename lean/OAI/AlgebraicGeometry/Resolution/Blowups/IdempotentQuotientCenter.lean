import OAI.AlgebraicGeometry.Resolution.Blowups.ZeroDimensionalCoefficientCenter
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Idempotent Quotient Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IdempotentQuotientCenter.Construction

noncomputable section

/-! Two principal neighborhoods for centers inside a zero-dimensional reduced hypersurface. -/

variable {R : Type*} [CommRing R]

/-- Lifting the idempotent generator of the quotient center gives two ambient
generators, with their product relation lying in the hypersurface equation. -/
theorem zero_dimensional_hypersurface_center_generators (z : R)
    [IsNoetherianRing (R ⧸ Ideal.span {z})] [IsReduced (R ⧸ Ideal.span {z})]
    (hd : ringKrullDim (R ⧸ Ideal.span {z}) ≤ 0) (I : Ideal R) (hz : z ∈ I) :
    ∃ r ∈ I, I = Ideal.span {r} ⊔ Ideal.span {z} ∧ r * (1 - r) ∈ Ideal.span {z} := by
  let q := Ideal.Quotient.mk (Ideal.span {z})
  obtain ⟨e, he, hC⟩ := ZeroDimensionalCoefficientCenter.Construction.zero_dimensional_ideal_idempotent_generator hd (I.map q)
  have heC : e ∈ I.map q := hC.symm ▸ Ideal.mem_span_singleton_self e
  obtain ⟨r, hr, hqr⟩ := (Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp heC
  have hrel : r * (1 - r) ∈ Ideal.span {z} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (r * (1 - r)) = 0
    rw [map_mul, map_sub, map_one, hqr, mul_sub, mul_one, he.eq, sub_self]
  refine ⟨r, hr, ?_, hrel⟩
  apply le_antisymm
  · intro x hx
    have hqx : q x ∈ Ideal.span {e} := hC ▸ Ideal.mem_map_of_mem q hx
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hqx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hdiff : x - r * a ∈ Ideal.span {z} := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change q (x - r * a) = 0
      rw [map_sub, map_mul, hqr, hc, sub_self]
    have hrmul : r * a ∈ Ideal.span {r} := Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self r)
    have hsum := (Ideal.span {r} ⊔ Ideal.span {z}).add_mem
      ((show Ideal.span {z} ≤ Ideal.span {r} ⊔ Ideal.span {z} from le_sup_right) hdiff)
      ((show Ideal.span {r} ≤ Ideal.span {r} ⊔ Ideal.span {z} from le_sup_left) hrmul)
    simpa only [sub_add_cancel] using hsum
  · exact sup_le ((Ideal.span_singleton_le_iff_mem I).mpr hr)
      ((Ideal.span_singleton_le_iff_mem I).mpr hz)

/-- On the open where the lifted idempotent is invertible, the center ideal
is the unit ideal. -/
theorem center_map_away_member_eq_top (I : Ideal R) (r : R) (hr : r ∈ I) :
    I.map (algebraMap R (Localization.Away r)) = ⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hr)
  exact IsLocalization.Away.algebraMap_isUnit r

/-- On the complementary principal neighborhood, the hypersurface equation
alone generates the center. -/
theorem idempotent_quotient_center_map_complement (I : Ideal R) (r z : R)
    (hI : I = Ideal.span {r} ⊔ Ideal.span {z}) (hrel : r * (1 - r) ∈ Ideal.span {z}) :
    I.map (algebraMap R (Localization.Away (1 - r))) =
      Ideal.span {algebraMap R (Localization.Away (1 - r)) z} := by
  let S := Localization.Away (1 - r)
  let f := algebraMap R S
  have hunit : IsUnit (f (1 - r)) := IsLocalization.Away.algebraMap_isUnit (1 - r)
  obtain ⟨u, hu⟩ := hunit
  have hprod : f r * f (1 - r) ∈ Ideal.span {f z} := by
    have h := Ideal.mem_map_of_mem f hrel
    simpa only [map_mul, Ideal.map_span, Set.image_singleton] using h
  have hr : f r ∈ Ideal.span {f z} := by
    have h := (Ideal.span {f z}).mul_mem_right (↑u⁻¹ : S) hprod
    rw [← hu, mul_assoc, Units.mul_inv, mul_one] at h
    exact h
  rw [hI, Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
  exact sup_eq_right.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hr)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IdempotentQuotientCenter.Construction
