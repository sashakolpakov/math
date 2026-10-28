import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ImageFunctions

/-! # Nonvanishing Map Functions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonvanishingMapFunctions

noncomputable section

/-!
The map between nonvanishing subschemes has the usual restriction formula on
functions. This identifies chart-extension coefficients with restrictions of
one fixed function on the original nonvanishing open.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {L : Y.Modules}

theorem sectionNonvanishingMap_eq_resLE (s : Line.Bundles.structureModule Y ⟶ L) :
    NonvanishingRestrictionMap.sectionNonvanishingMap f s = f.resLE (Ample.LineBundles.sectionNonvanishing s)
      (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)) (Section.Nonvanishing.sectionNonvanishing_pullback f s).le := by
  apply (cancel_mono (Ample.LineBundles.sectionNonvanishing s).ι).mp
  exact (NonvanishingRestrictionMap.sectionNonvanishingMap_ι f s).trans
    (Scheme.Hom.resLE_comp_ι f (Section.Nonvanishing.sectionNonvanishing_pullback f s).le).symm

/-- Normalize the source and target open-subscheme functions using their canonical top isomorphisms. -/
theorem sectionNonvanishingMap_appTop (s : Line.Bundles.structureModule Y ⟶ L) :
    (NonvanishingRestrictionMap.sectionNonvanishingMap f s).appTop ≫ (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).topIso.hom =
      (Ample.LineBundles.sectionNonvanishing s).topIso.hom ≫ f.appLE (Ample.LineBundles.sectionNonvanishing s)
        (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)) (Section.Nonvanishing.sectionNonvanishing_pullback f s).le := by
  let D := Ample.LineBundles.sectionNonvanishing s
  let V := Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)
  have hg : (NonvanishingRestrictionMap.sectionNonvanishingMap f s).appTop =
      D.topIso.hom ≫ f.appLE D V (Section.Nonvanishing.sectionNonvanishing_pullback f s).le ≫ V.topIso.inv :=
    (congrArg (fun g => g.appTop) (sectionNonvanishingMap_eq_resLE f s)).trans
      (Scheme.Hom.resLE_app_top f (Section.Nonvanishing.sectionNonvanishing_pullback f s).le)
  exact (congrArg (fun a => a ≫ V.topIso.hom) hg).trans
    (by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]; rfl)

/-- The image of a pulled-back nonvanishing open is contained in the original one. -/
theorem sectionNonvanishing_image_le (s : Line.Bundles.structureModule Y ⟶ L) :
    f ''ᵁ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s) ≤ Ample.LineBundles.sectionNonvanishing s := by
  rw [Section.Nonvanishing.sectionNonvanishing_pullback, Scheme.Hom.image_preimage_eq_opensRange_inf]
  exact inf_le_right

/-- Expressing a function on the original `D(s)` through a chart gives exactly
its ordinary restriction to the chart's image inside `D(s)`. -/
theorem sectionNonvanishingMap_imageFunction (s : Line.Bundles.structureModule Y ⟶ L)
    (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) :
    (f.appIso (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s))).inv
      ((Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).topIso.hom ((NonvanishingRestrictionMap.sectionNonvanishingMap f s).appTop r)) =
        Y.presheaf.map (homOfLE (sectionNonvanishing_image_le f s)).op
          ((Ample.LineBundles.sectionNonvanishing s).topIso.hom r) := by
  let D := Ample.LineBundles.sectionNonvanishing s
  let V := Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)
  have h₀ := ConcreteCategory.congr_hom (sectionNonvanishingMap_appTop f s) r
  have h₁ : f.appLE D V (Section.Nonvanishing.sectionNonvanishing_pullback f s).le ≫ (f.appIso V).inv =
      Y.presheaf.map (homOfLE (sectionNonvanishing_image_le f s)).op :=
    f.appLE_appIso_inv (Section.Nonvanishing.sectionNonvanishing_pullback f s).le
  exact (congrArg (fun a : Γ(X, V) => (f.appIso V).inv a) h₀).trans
    (ConcreteCategory.congr_hom h₁ (D.topIso.hom r))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonvanishingMapFunctions
