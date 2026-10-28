import OAI.AlgebraicGeometry.Resolution.Blowups.ChartLift

/-! # Chart Generator Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartGeneratorComparison.Construction

noncomputable section

/-! The original coefficients and degree-one ratios determine maps from the actual Rees chart into any ring. -/

universe u v

theorem blowupChart_hom_ext_of_constants_ratios
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] (I : Ideal R) (a : I)
    (f g : Charts.Construction.blowupChart I a →+* S)
    (hconstants : ∀ r : R, f (Charts.Construction.blowupChartConstants I a r) = g (Charts.Construction.blowupChartConstants I a r))
    (hratios : ∀ b : I, f (ExceptionalIdeal.Construction.blowupChartRatio I a b) = g (ExceptionalIdeal.Construction.blowupChartRatio I a b)) : f = g := by
  let χ := Charts.Construction.blowupChartToLocalization I a
  let B : Subalgebra R (Localization.Away a.val) :=
    { carrier := {z | ∃ x : Charts.Construction.blowupChart I a, f x = g x ∧ χ x = z}
      zero_mem' := ⟨0, by simp, by simp⟩
      one_mem' := ⟨1, by simp, by simp⟩
      add_mem' := by
        rintro z w ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, by simp only [map_add, hx, hy], map_add χ x y⟩
      mul_mem' := by
        rintro z w ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, by simp only [map_mul, hx, hy], map_mul χ x y⟩
      algebraMap_mem' := fun r => ⟨Charts.Construction.blowupChartConstants I a r, hconstants r, Charts.Construction.blowupChartToLocalization_constants I a r⟩ }
  have hle : Charts.Construction.blowupChartImage I a ≤ B := by
    rw [Charts.Construction.blowupChartImage_eq_adjoin]
    apply Algebra.adjoin_le
    rintro _ ⟨b, rfl⟩
    exact ⟨ExceptionalIdeal.Construction.blowupChartRatio I a b, hratios b, ExceptionalIdeal.Construction.blowupChartToLocalization_ratio I a b⟩
  ext x
  obtain ⟨y, hy, he⟩ := hle (show χ x ∈ Charts.Construction.blowupChartImage I a from ⟨x, rfl⟩)
  have hyx : y = x := Charts.Construction.blowupChartToLocalization_injective I a he
  exact hyx ▸ hy

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartGeneratorComparison.Construction
