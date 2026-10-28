import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.LocalOne
import Mathlib.RingTheory.KrullDimension.Regular

/-! # Local Two Parameters -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.LocalTwoParameters

noncomputable section

/-! In a two-dimensional regular local domain, a minimal pair of
generators of the maximal ideal is an actual regular sequence. -/

open IsLocalRing

universe u

variable (R : Type u) [CommRing R] [IsRegularLocalRing R] [IsDomain R]

theorem exists_pair (hd : ringKrullDim R = 2) :
    ∃ a b : R, a ≠ 0 ∧ maximalIdeal R = Ideal.span {a, b} ∧
      IsSMulRegular (R ⧸ Ideal.span {a}) b := by
  classical
  have hspan : (maximalIdeal R).spanFinrank = 2 := by
    have h := ((isRegularLocalRing_iff R).mp inferInstance).trans hd
    exact_mod_cast h
  have hn (c : R) : maximalIdeal R ≠ Ideal.span {c} := by
    intro hc
    have hle := Submodule.spanFinrank_span_le_ncard_of_finite
      (R := R) (Set.finite_singleton c)
    change (Ideal.span {c}).spanFinrank ≤ _ at hle
    rw [← hc, hspan, Set.ncard_singleton] at hle
    omega
  obtain ⟨s, hs, hsm⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (maximalIdeal R).fg_of_isNoetherianRing
  rw [hspan] at hs
  obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp hs
  have hm : maximalIdeal R = Ideal.span {a, b} := by simpa only [Finset.coe_pair] using hsm.symm
  have ha : a ≠ 0 := by
    intro ha
    apply hn b
    simpa [ha] using hm
  have ham : a ∈ maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
  have hIa : Ideal.span {a} ≤ maximalIdeal R :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ham)
  let S := R ⧸ Ideal.span {a}
  let π : R →+* S := Ideal.Quotient.mk _
  let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIa)
  let : IsLocalRing S := IsLocalRing.of_surjective' π Ideal.Quotient.mk_surjective
  have hms : maximalIdeal S = Ideal.span {π b} := by
    rw [← map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective, hm, Ideal.map_span]
    have hpa : π a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simp [Set.image_insert_eq, Set.image_singleton, hpa]
  have hdim : ringKrullDim S = 1 := by
    have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
      (show IsSMulRegular R a from fun _ _ h => mul_left_cancel₀ ha h) ham
    rw [hd] at h
    apply (ENat.WithBot.add_natCast_cancel (c := 1)).mp
    change ringKrullDim S + 1 = 1 + 1
    simpa only [one_add_one_eq_two] using h
  let : IsDomain S := LocalOne.domain_of_principal S ⟨π b, hms⟩
    (hdim ▸ by norm_num)
  have hb : π b ≠ 0 := by
    intro hb
    apply hn a
    apply le_antisymm
    · rw [hm]
      apply Ideal.span_le.mpr
      intro c hc
      rcases hc with rfl | hc
      · exact Ideal.subset_span (by simp)
      · have hc' : c = b := Set.mem_singleton_iff.mp hc
        rw [hc']
        exact Ideal.Quotient.eq_zero_iff_mem.mp hb
    · exact hIa
  refine ⟨a, b, ha, hm, ?_⟩
  intro x y hxy
  exact mul_left_cancel₀ hb hxy

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.LocalTwoParameters
