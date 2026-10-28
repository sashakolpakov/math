import OAI.AlgebraicGeometry.Resolution.Blowups.Open.ImmersionSmoothImage
import OAI.AlgebraicGeometry.Resolution.Blowups.SchemeImageClosedComposition

/-! # Strict Image Criterion -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.StrictImageCriterion.Construction

noncomputable section

/-! Smoothness of the actual strict image from an open part of a smooth closed carrier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem schemeImage_smooth_of_open_closed_factorization {V W Y : Scheme}
    (j : V ⟶ W) [IsOpenImmersion j] [QuasiCompact j] [IsReduced V]
    (i : W ⟶ Y) [IsClosedImmersion i] (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth (i ≫ f)] :
    Smooth ((j ≫ i).imageι ≫ f) := by
  obtain ⟨e, he⟩ := SchemeImageClosedComposition.Construction.schemeImage_closed_composition_iso j i
  let : Smooth (j.imageι ≫ (i ≫ f)) := Open.ImmersionSmoothImage.Construction.openImmersion_image_smooth_complex j (i ≫ f)
  have hf : e.hom ≫ ((j ≫ i).imageι ≫ f) = j.imageι ≫ (i ≫ f) := by
    rw [← Category.assoc, he, Category.assoc]
  let : Smooth (e.hom ≫ ((j ≫ i).imageι ≫ f)) := hf.symm ▸ inferInstance
  have ht : e.inv ≫ (e.hom ≫ ((j ≫ i).imageι ≫ f)) = (j ≫ i).imageι ≫ f :=
    e.inv_hom_id_assoc _
  exact ht ▸ inferInstanceAs (Smooth (e.inv ≫ (e.hom ≫ ((j ≫ i).imageι ≫ f))))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.StrictImageCriterion.Construction
