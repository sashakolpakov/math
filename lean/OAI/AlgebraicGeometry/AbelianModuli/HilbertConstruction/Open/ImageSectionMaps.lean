import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionsOnOpenImages
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FrameTransport

/-! # Image Section Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ImageSectionMaps

noncomputable section

/-!
Normalize pulled-back sections into explicit restrictions. Normalization
preserves local ratios and commutes with maps of the original module sheaves.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}

/-- Express a canonical pullback section in the explicit restriction sheaf. -/
def normalizedPullbackSection
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M) :
    Line.Bundles.structureModule X ⟶ M.restrict f :=
  (SectionsOnOpenImages.pullbackImageSourceIso f).hom ≫ t ≫ ((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv

theorem pullbackSectionImageEquiv_eq
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M) :
    SectionsOnOpenImages.pullbackSectionImageEquiv f M t = Global.Sections.moduleSectionHomEquiv (M.restrict f) (normalizedPullbackSection f t) :=
  rfl

theorem normalizedPullbackSection_pullback (s : Line.Bundles.structureModule Y ⟶ M) :
    normalizedPullbackSection f (Ample.LineBundles.pullbackSection f s) = Section.SectionRestriction.restrictSection f s := by
  apply (Global.Sections.moduleSectionHomEquiv (M.restrict f)).injective
  exact (SectionsOnOpenImages.pullbackSectionImageEquiv_pullback f M s).trans (Section.SectionRestriction.restrictSection_app_one f s ⊤).symm

/-- Normalization preserves ratios after any further pullback. -/
theorem normalizedPullbackSection_ratio (h : Z ⟶ X)
    (s t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M)
    [hs : IsIso (Ample.LineBundles.pullbackSection h s)] :
    letI : IsIso (Ample.LineBundles.pullbackSection h (normalizedPullbackSection f s)) :=
      @Section.FrameTransport.pullbackSection_frameTransport_isIso Z X h _ _ (SectionsOnOpenImages.pullbackImageSourceIso f)
        ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm s hs
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection h (normalizedPullbackSection f s))
      (Ample.LineBundles.pullbackSection h (normalizedPullbackSection f t)) =
        Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection h s) (Ample.LineBundles.pullbackSection h t) :=
  @Section.FrameTransport.frameCoordinate_pullback_frameTransport Z X h _ _ (SectionsOnOpenImages.pullbackImageSourceIso f)
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm s t hs

/-- Maps of the original module sheaves commute with normalization. -/
theorem normalizedPullbackSection_postcomp
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M) (a : M ⟶ N) :
    normalizedPullbackSection f (t ≫ (Scheme.Modules.pullback f).map a) =
      normalizedPullbackSection f t ≫ (Scheme.Modules.restrictFunctor f).map a := by
  let E := Scheme.Modules.restrictFunctorIsoPullback f
  let E₀ : M.restrict f ≅ (Scheme.Modules.pullback f).obj M := E.app M
  let E₁ : N.restrict f ≅ (Scheme.Modules.pullback f).obj N := E.app N
  have hn : (Scheme.Modules.restrictFunctor f).map a ≫ E₁.hom =
      E₀.hom ≫ (Scheme.Modules.pullback f).map a := E.hom.naturality a
  have ha : (Scheme.Modules.pullback f).map a ≫ E₁.inv = E₀.inv ≫ (Scheme.Modules.restrictFunctor f).map a := by
    calc
      _ = E₀.inv ≫ (E₀.hom ≫ (Scheme.Modules.pullback f).map a) ≫ E₁.inv := by
        simp only [Category.assoc, E₀.inv_hom_id_assoc]
      _ = E₀.inv ≫ ((Scheme.Modules.restrictFunctor f).map a ≫ E₁.hom) ≫ E₁.inv :=
        congrArg (fun z => E₀.inv ≫ z ≫ E₁.inv) hn.symm
      _ = E₀.inv ≫ (Scheme.Modules.restrictFunctor f).map a := by
        rw [Category.assoc, E₁.hom_inv_id, Category.comp_id]
  change (SectionsOnOpenImages.pullbackImageSourceIso f).hom ≫ (t ≫ (Scheme.Modules.pullback f).map a) ≫ E₁.inv =
    ((SectionsOnOpenImages.pullbackImageSourceIso f).hom ≫ t ≫ E₀.inv) ≫ (Scheme.Modules.restrictFunctor f).map a
  simp only [Category.assoc]
  rw [ha]

/-- On image-open sections, applying a module map is the usual component map. -/
theorem pullbackSectionImageEquiv_postcomp
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M) (a : M ⟶ N) :
    SectionsOnOpenImages.pullbackSectionImageEquiv f N (t ≫ (Scheme.Modules.pullback f).map a) =
      a.app (f ''ᵁ ⊤) (SectionsOnOpenImages.pullbackSectionImageEquiv f M t) :=
  congrArg (Global.Sections.moduleSectionHomEquiv (N.restrict f)) (normalizedPullbackSection_postcomp f t a)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ImageSectionMaps
