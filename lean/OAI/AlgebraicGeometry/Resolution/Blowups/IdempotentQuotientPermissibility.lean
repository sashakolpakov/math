import OAI.AlgebraicGeometry.Resolution.Blowups.IdempotentQuotientCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.EulerOrderCriterion
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalizedIdealContainment

/-! # Idempotent Quotient Permissibility -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IdempotentQuotientPermissibility.Construction

noncomputable section

/-! Permissibility of hypersurface centers cut out by idempotents on the hypersurface. -/

variable {R : Type*} [CommRing R]

theorem idempotent_hypersurface_center_generators (z : R) (I : Ideal R) (hz : z ∈ I)
    (hgen : ∃ e : R ⧸ Ideal.span {z}, IsIdempotentElem e ∧
      I.map (Ideal.Quotient.mk (Ideal.span {z})) = Ideal.span {e}) :
    ∃ r ∈ I, I = Ideal.span {r} ⊔ Ideal.span {z} ∧ r * (1 - r) ∈ Ideal.span {z} := by
  let q := Ideal.Quotient.mk (Ideal.span {z})
  obtain ⟨e, he, hC⟩ := hgen
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

theorem idempotent_quotient_center_permissible
    {k : Type*} [CommRing k] [Algebra k R] [Algebra ℚ R]
    (E : Derivation k R R) (z : R) (hz : E z = 1)
    (I J : Ideal R) (r : R) (hr : r ∈ I)
    (hI : I = Ideal.span {r} ⊔ Ideal.span {z})
    (hrel : r * (1 - r) ∈ Ideal.span {z}) (n : ℕ)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n ≤ I) : J ≤ I ^ (n + 1) := by
  have hcover : Ideal.span ({r, 1 - r} : Set R) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have h := (Ideal.span ({r, 1 - r} : Set R)).add_mem
      (Ideal.subset_span (Set.mem_insert r {1 - r}))
      (Ideal.subset_span (Set.mem_insert_of_mem r (Set.mem_singleton (1 - r))))
    simpa only [add_sub_cancel] using h
  apply LocalizedIdealContainment.Construction.ideal_le_of_localized_away_cover J (I ^ (n + 1)) {r, 1 - r} hcover
  intro s hs
  rcases Set.mem_insert_iff.mp hs with hs | hs
  · subst s
    rw [Ideal.map_pow, IdempotentQuotientCenter.Construction.center_map_away_member_eq_top I r hr, Ideal.top_pow]
    exact le_top
  · have heq : s = 1 - r := Set.mem_singleton_iff.mp hs
    subst s
    let A := Localization.Away (1 - r)
    let : Algebra.Etale R A := Algebra.Etale.of_isLocalizationAway (1 - r)
    have hm := IdempotentQuotientCenter.Construction.idempotent_quotient_center_map_complement I r z hI hrel
    rw [Ideal.map_pow, hm]
    have heuler := Relative.EulerOrderCriterion.Construction.mapped_coordinate_order_iff_relative_differentialIdeal
      (B := A) (fun _ : Unit => z) (fun _ : Unit => E)
      (by intro i j; cases i; cases j; simpa using hz) J n
    simp only [Set.range_const] at heuler
    apply heuler.mpr
    exact (Ideal.map_mono hbound).trans_eq hm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IdempotentQuotientPermissibility.Construction
