import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.SchemeImage

/-! # Scheme Image Closed Composition -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.SchemeImageClosedComposition.Construction

noncomputable section

/-! Taking the actual scheme image commutes with a closed immersion of the target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem schemeImage_closed_composition_kernel {V Y X : Scheme.{u}}
    (j : V ⟶ Y) [QuasiCompact j] [IsReduced V] (i : Y ⟶ X) :
    (j.imageι ≫ i).ker = (j ≫ i).ker := by
  let : IsReduced j.image := Integral.SchemeImage.Construction.scheme_image_isReduced j
  let : IsSchemeTheoreticallyDominant j.toImage := IsSchemeTheoreticallyDominant.of_isDominant j.toImage
  have he : j.toImage ≫ (j.imageι ≫ i) = j ≫ i := by
    rw [← Category.assoc, j.toImage_imageι]
  have hk := Scheme.Hom.ker_comp j.toImage (j.imageι ≫ i)
  rw [j.toImage.ker_eq_bot, Scheme.IdealSheafData.map_bot, he] at hk
  exact hk.symm

theorem schemeImage_closed_composition_iso {V Y X : Scheme.{u}}
    (j : V ⟶ Y) [QuasiCompact j] [IsReduced V] (i : Y ⟶ X) [IsClosedImmersion i] :
    ∃ e : j.image ≅ (j ≫ i).image, e.hom ≫ (j ≫ i).imageι = j.imageι ≫ i := by
  have hk : (j.imageι ≫ i).ker = (j ≫ i).imageι.ker := by
    rw [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι]
    exact schemeImage_closed_composition_kernel j i
  let a := IsClosedImmersion.lift (j ≫ i).imageι (j.imageι ≫ i) hk.symm.le
  let : IsIso a := IsClosedImmersion.isIso_of_ker_eq (j.imageι ≫ i) (j ≫ i).imageι a
    (IsClosedImmersion.lift_fac _ _ _) hk
  exact ⟨asIso a, IsClosedImmersion.lift_fac _ _ _⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.SchemeImageClosedComposition.Construction
