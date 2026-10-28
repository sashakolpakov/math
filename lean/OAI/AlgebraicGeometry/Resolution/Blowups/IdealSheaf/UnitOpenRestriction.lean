import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealChartDescent

/-! # Unit Open Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.UnitOpenRestriction.Construction

noncomputable section

/-! A unit restriction stays a unit along every map whose image lies in that open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem idealSheaf_comap_top_of_image_in_open
    {X V : Scheme} (I : X.IdealSheafData) (O : X.Opens) (hO : I.comap O.ι = ⊤)
    (j : V ⟶ X) (hj : ∀ y, j y ∈ O) : I.comap j = ⊤ := by
  have hrange : Set.range j ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hj y
  let a := IsOpenImmersion.lift O.ι j hrange
  have ha : a ≫ O.ι = j := IsOpenImmersion.lift_fac _ _ _
  rw [← ha, Scheme.IdealSheafData.comap_comp, hO, Scheme.IdealSheafData.comap_top]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.UnitOpenRestriction.Construction
