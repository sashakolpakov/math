import OAI.AlgebraicGeometry.Resolution.Blowups.IdempotentQuotientCenter

/-! # General Idempotent Quotient Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GeneralIdempotentQuotientCenter.Construction

noncomputable section

/-! Open generators for an arbitrary center over a reduced zero-dimensional quotient. -/

variable {R : Type*} [CommRing R]

theorem zero_dimensional_quotient_center_generators (K : Ideal R)
    [IsNoetherianRing (R ⧸ K)] [IsReduced (R ⧸ K)]
    (hd : ringKrullDim (R ⧸ K) ≤ 0) (I : Ideal R) (hK : K ≤ I) :
    ∃ r ∈ I, I = Ideal.span {r} ⊔ K ∧ r * (1 - r) ∈ K := by
  let q := Ideal.Quotient.mk (K)
  obtain ⟨e, he, hC⟩ := ZeroDimensionalCoefficientCenter.Construction.zero_dimensional_ideal_idempotent_generator hd (I.map q)
  have heC : e ∈ I.map q := hC.symm ▸ Ideal.mem_span_singleton_self e
  obtain ⟨r, hr, hqr⟩ := (Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp heC
  have hrel : r * (1 - r) ∈ K := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (r * (1 - r)) = 0
    rw [map_mul, map_sub, map_one, hqr, mul_sub, mul_one, he.eq, sub_self]
  refine ⟨r, hr, ?_, hrel⟩
  apply le_antisymm
  · intro x hx
    have hqx : q x ∈ Ideal.span {e} := hC ▸ Ideal.mem_map_of_mem q hx
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hqx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hdiff : x - r * a ∈ K := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change q (x - r * a) = 0
      rw [map_sub, map_mul, hqr, hc, sub_self]
    have hrmul : r * a ∈ Ideal.span {r} := Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self r)
    have hsum := (Ideal.span {r} ⊔ K).add_mem
      ((show K ≤ Ideal.span {r} ⊔ K from le_sup_right) hdiff)
      ((show Ideal.span {r} ≤ Ideal.span {r} ⊔ K from le_sup_left) hrmul)
    simpa only [sub_add_cancel] using hsum
  · exact sup_le ((Ideal.span_singleton_le_iff_mem I).mpr hr)
      hK

theorem idempotent_general_quotient_center_map_complement (I K : Ideal R) (r : R)
    (hI : I = Ideal.span {r} ⊔ K) (hrel : r * (1 - r) ∈ K) :
    I.map (algebraMap R (Localization.Away (1 - r))) =
      K.map (algebraMap R (Localization.Away (1 - r))) := by
  let S := Localization.Away (1 - r)
  let f := algebraMap R S
  obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (R := R) (S := S) (1 - r)
  have hprod : f r * f (1 - r) ∈ K.map f := by
    simpa only [map_mul] using Ideal.mem_map_of_mem f hrel
  have hr : f r ∈ K.map f := by
    have h := (K.map f).mul_mem_right (↑u⁻¹ : S) hprod
    rw [← hu, mul_assoc, Units.mul_inv, mul_one] at h
    exact h
  rw [hI, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  exact sup_eq_right.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hr)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GeneralIdempotentQuotientCenter.Construction
