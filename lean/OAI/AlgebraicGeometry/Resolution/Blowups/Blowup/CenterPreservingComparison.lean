import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.TangentComparisonCongruence

/-! # Center Preserving Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.CenterPreservingComparison.Construction

noncomputable section

/-! Two tangent-congruent comparison maps preserve every later permissible center on a common blowup chart. -/

universe u v

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem blowupChart_center_preserving_comparison
    (k : Type*) [CommRing k] {R : Type u} [CommRing R] [Algebra k R]
    {S : Type v} [CommRing S] (I J : Ideal R) (a : I) (n : ℕ) (hp : J ≤ I ^ (n + 1))
    (f g : Charts.Construction.blowupChart I a →+* S)
    (hregular : IsRegular (f (Charts.Construction.blowupChartConstants I a a.val)))
    (u : Sˣ) (hu : g (Charts.Construction.blowupChartConstants I a a.val) = f (Charts.Construction.blowupChartConstants I a a.val) * u)
    (hT : (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (f.comp (Charts.Construction.blowupChartConstants I a)) =
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (g.comp (Charts.Construction.blowupChartConstants I a)))
    (hdiff : ∀ r : R, g (Charts.Construction.blowupChartConstants I a r) - f (Charts.Construction.blowupChartConstants I a r) ∈
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (f.comp (Charts.Construction.blowupChartConstants I a))) :
    let T' := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n
    T'.map f = T'.map g ∧ (∀ x : Charts.Construction.blowupChart I a, g x - f x ∈ T'.map f) ∧
      ∀ L : Ideal (Charts.Construction.blowupChart I a), ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a ≤ L ^ (n + 1) → L.map f = L.map g := by
  let T' := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n
  have hfg := TangentComparisonCongruence.Construction.blowupChart_tangent_congruence k I J a n hp f g hregular u hu hdiff
  have hregular' : IsRegular (g (Charts.Construction.blowupChartConstants I a a.val)) := by
    rw [hu]
    exact hregular.mul u.isUnit.isRegular
  have hu' : f (Charts.Construction.blowupChartConstants I a a.val) = g (Charts.Construction.blowupChartConstants I a a.val) * (u⁻¹ : Sˣ) := by
    rw [hu, mul_assoc, Units.mul_inv, mul_one]
  have hdiff' (r : R) : f (Charts.Construction.blowupChartConstants I a r) - g (Charts.Construction.blowupChartConstants I a r) ∈
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (g.comp (Charts.Construction.blowupChartConstants I a)) := by
    rw [← hT]
    simpa only [neg_sub] using
      ((Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (f.comp (Charts.Construction.blowupChartConstants I a))).neg_mem (hdiff r)
  have hgf := TangentComparisonCongruence.Construction.blowupChart_tangent_congruence k I J a n hp g f hregular' u⁻¹ hu' hdiff'
  have he : T'.map f = T'.map g := by
    apply le_antisymm
    · apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      change f x ∈ T'.map g
      simpa only [sub_add_cancel] using (T'.map g).add_mem (hgf x) (Ideal.mem_map_of_mem g hx)
    · apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      change g x ∈ T'.map f
      simpa only [sub_add_cancel] using (T'.map f).add_mem (hfg x) (Ideal.mem_map_of_mem f hx)
  refine ⟨he, hfg, ?_⟩
  intro L hL
  exact Blowups.Ideal.ImageCongruence.Construction.ideal_images_eq_of_congruence f g T' L he hfg
    (Blowups.Ideal.ImageCongruence.Construction.relative_tangent_le_permissible_center k (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) L n hL)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.CenterPreservingComparison.Construction
