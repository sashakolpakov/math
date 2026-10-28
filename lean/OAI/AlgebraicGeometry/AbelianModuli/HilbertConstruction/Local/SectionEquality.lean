import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ImageSectionMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoordinatesOnOpenSubschemes

/-! # Section Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.SectionEquality

noncomputable section

/-! Equality and vanishing of local sections expressed by their ordinary sheaf values. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {M : Y.Modules}

theorem pullbackSectionImageEquiv_zero (f : X ⟶ Y) [IsOpenImmersion f] :
    SectionsOnOpenImages.pullbackSectionImageEquiv f M 0 = 0 := by
  change Global.Sections.moduleSectionHomEquiv (M.restrict f)
    ((SectionsOnOpenImages.pullbackImageSourceIso f).hom ≫ 0 ≫
      ((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv) = 0
  simp only [zero_comp, comp_zero, Global.Sections.moduleSectionHomEquiv_apply]
  rfl

/-- A pulled-back section vanishes exactly when its value on the image open vanishes. -/
theorem pullbackSection_eq_zero_iff_image (f : X ⟶ Y) [IsOpenImmersion f]
    (s : Line.Bundles.structureModule Y ⟶ M) :
    Ample.LineBundles.pullbackSection f s = 0 ↔ s.app (f ''ᵁ ⊤) (1 : Γ(Y, f ''ᵁ ⊤)) = 0 := by
  rw [← (SectionsOnOpenImages.pullbackSectionImageEquiv f M).injective.eq_iff,
    SectionsOnOpenImages.pullbackSectionImageEquiv_pullback, pullbackSectionImageEquiv_zero]

/-- Vanishing on an open subscheme is vanishing of the section value on that open. -/
theorem pullbackSection_eq_zero_iff_on_open (U : Y.Opens)
    (s : Line.Bundles.structureModule Y ⟶ M) :
    Ample.LineBundles.pullbackSection U.ι s = 0 ↔ s.app U (1 : Γ(Y, U)) = 0 := by
  have h := pullbackSection_eq_zero_iff_image U.ι s
  exact h.trans (congrArg (fun V : Y.Opens => s.app V (1 : Γ(Y, V)) = 0)
    U.ι_image_top).to_iff

/-- Equality of canonical pullbacks can be tested on ordinary section values. -/
theorem pullbackSection_eq_iff_on_open (U : Y.Opens)
    (s t : Line.Bundles.structureModule Y ⟶ M) :
    Ample.LineBundles.pullbackSection U.ι s = Ample.LineBundles.pullbackSection U.ι t ↔
      s.app U (1 : Γ(Y, U)) = t.app U (1 : Γ(Y, U)) := by
  rw [← (SectionsOnOpenImages.pullbackSectionImageEquiv U.ι M).injective.eq_iff,
    SectionsOnOpenImages.pullbackSectionImageEquiv_pullback, SectionsOnOpenImages.pullbackSectionImageEquiv_pullback]
  exact (congrArg (fun V : Y.Opens => s.app V (1 : Γ(Y, V)) = t.app V (1 : Γ(Y, V)))
    U.ι_image_top).to_iff

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.SectionEquality
