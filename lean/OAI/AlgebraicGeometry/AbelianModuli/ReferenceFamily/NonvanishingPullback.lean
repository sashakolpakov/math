import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.CoordinatePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing

/-! # Nonvanishing Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NonvanishingPullback

noncomputable section

/-! Nonvanishing of line-bundle sections commutes with arbitrary scheme
pullback, as follows from regular coordinates in local frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing

universe u
variable {X Y Z : Scheme.{u}}

theorem sectionNonvanishing_pullback_comp (f : Y ⟶ Z) (h : X ⟶ Y)
    {L : Z.Modules} (s : HilbertConstruction.Line.Bundles.structureModule Z ⟶ L) :
    HilbertConstruction.Ample.LineBundles.sectionNonvanishing (HilbertConstruction.Ample.LineBundles.pullbackSection h (HilbertConstruction.Ample.LineBundles.pullbackSection f s)) =
      HilbertConstruction.Ample.LineBundles.sectionNonvanishing (HilbertConstruction.Ample.LineBundles.pullbackSection (h ≫ f) s) := by
  unfold HilbertConstruction.Ample.LineBundles.sectionNonvanishing
  apply congrArg sSup
  ext U
  change IsIso (HilbertConstruction.Ample.LineBundles.pullbackSection U.ι (HilbertConstruction.Ample.LineBundles.pullbackSection h (HilbertConstruction.Ample.LineBundles.pullbackSection f s))) ↔
    IsIso (HilbertConstruction.Ample.LineBundles.pullbackSection U.ι (HilbertConstruction.Ample.LineBundles.pullbackSection (h ≫ f) s))
  rw [HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_comp_iff, HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_comp_iff,
    HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_comp_iff, Category.assoc]

theorem sectionNonvanishing_pullback_framed (f : X ⟶ Y) {L : Y.Modules}
    (s t : HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) [IsIso s] :
    HilbertConstruction.Ample.LineBundles.sectionNonvanishing (HilbertConstruction.Ample.LineBundles.pullbackSection f t) = f ⁻¹ᵁ HilbertConstruction.Ample.LineBundles.sectionNonvanishing t := by
  rw [HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate (HilbertConstruction.Ample.LineBundles.pullbackSection f s),
    Frame.CoordinatePullback.frameCoordinate_pullback_any, HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate s,
    f.preimage_basicOpen_top]

theorem sectionNonvanishing_pullback_restrict (f : X ⟶ Y) (U : Y.Opens)
    {L : Y.Modules} (s : HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) :
    HilbertConstruction.Ample.LineBundles.sectionNonvanishing (HilbertConstruction.Ample.LineBundles.pullbackSection (f ∣_ U) (HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s)) =
      HilbertConstruction.Ample.LineBundles.sectionNonvanishing (HilbertConstruction.Ample.LineBundles.pullbackSection (f ⁻¹ᵁ U).ι (HilbertConstruction.Ample.LineBundles.pullbackSection f s)) := by
  rw [sectionNonvanishing_pullback_comp, sectionNonvanishing_pullback_comp,
    morphismRestrict_ι]

theorem lineBundle_sectionNonvanishing_pullback (f : X ⟶ Y) (L : HilbertConstruction.Line.Bundles.LineBundle Y)
    (s : HilbertConstruction.Line.Bundles.structureModule Y ⟶ L.sheaf) :
    HilbertConstruction.Ample.LineBundles.sectionNonvanishing (HilbertConstruction.Ample.LineBundles.pullbackSection f s) = f ⁻¹ᵁ HilbertConstruction.Ample.LineBundles.sectionNonvanishing s := by
  ext x
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyTrivial (f x)
  let y : (f ⁻¹ᵁ U).toScheme := ⟨x, hxU⟩
  have h := sectionNonvanishing_pullback_framed (f ∣_ U) e.inv (HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s)
  rw [sectionNonvanishing_pullback_restrict,
    HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback (f ⁻¹ᵁ U).ι,
    HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback U.ι] at h
  have hm := (congrArg (fun V : (f ⁻¹ᵁ U).toScheme.Opens => y ∈ V) h).to_iff
  change x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (HilbertConstruction.Ample.LineBundles.pullbackSection f s) ↔
    ((f ∣_ U) y).val ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing s at hm
  rw [morphismRestrict_base_coe] at hm
  exact hm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NonvanishingPullback
