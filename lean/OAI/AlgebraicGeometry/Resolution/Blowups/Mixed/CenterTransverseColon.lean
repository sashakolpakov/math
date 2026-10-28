import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CenterIncidence
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.TransverseRegularity
import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CenterDividedMembership

/-! # Center Transverse Colon -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A boundary equation transverse to a mixed smooth center is a nonzerodivisor modulo its ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts.transverse_colon
    {k : Type u} [Field k] (R : CommRingCat.{u}) [Algebra k R]
    (I : Ideal R) {β : Type v} {w : β → R} {F : Finset β}
    (h : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w F) (j : β) (hj : j ∉ F) :
    I.colon (Ideal.span {w j} : Set R) = I := by
  apply Boundary.TransverseRegularity.Construction.ideal_colon_eq_of_pointed_flat_charts
  intro p
  by_cases hp : I ≤ p.asIdeal
  · obtain ⟨C⟩ := h p hp
    have hf : Flat (Spec.map (CommRingCat.ofHom C.chart.map.toRingHom)) := inferInstance
    refine ⟨C.chart.carrier, C.chart.map.toRingHom,
      (HasRingHomProperty.Spec_iff (P := @Flat)).mp hf, C.chart.point, C.chart.point_over, ?_⟩
    rw [C.center_eq]
    exact FlatQuotientRegularity.Construction.ideal_colon_eq_of_quotient_regular _ _
      (C.chart.model.transverse_regular_mod_center C.coordinates F C.divided_iff j hj)
  · obtain ⟨a, ha, hap⟩ : ∃ a ∈ I, a ∉ p.asIdeal := by
      simpa only [SetLike.le_def, not_forall, exists_prop] using hp
    let S := Localization.Away a
    obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime a p hap
    have ht : I.map (algebraMap R S) = ⊤ := Ideal.eq_top_of_isUnit_mem _
      (Ideal.mem_map_of_mem (algebraMap R S) ha) (IsLocalization.Away.algebraMap_isUnit a)
    let : Algebra.Etale R S := Algebra.Etale.of_isLocalizationAway a
    refine ⟨.of S, algebraMap R S, RingHom.flat_algebraMap_iff.mpr inferInstance, Q, hQ, ?_⟩
    rw [ht]
    exact Submodule.top_colon

end

end OAI.AlgebraicGeometry.Resolution.Blowups
