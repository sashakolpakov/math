import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Comparison

/-! # Pullback Coherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.PullbackCoherence

noncomputable section

/-! Ratios are compatible with successive pullbacks and with restriction from a nonvanishing open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

/-- The structure-module frame for a composite module-pullback functor. -/
def structureModuleIteratedPullbackIso (f : Y ⟶ Z) (h : X ⟶ Y) :
    (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback f).obj (Line.Bundles.structureModule Z)) ≅
      Line.Bundles.structureModule X :=
  (Scheme.Modules.pullback h).mapIso (Line.Bundles.structureModulePullbackIso f) ≪≫ Line.Bundles.structureModulePullbackIso h

theorem section_iteratedPullback (f : Y ⟶ Z) (h : X ⟶ Y) {L : Z.Modules}
    (s : Line.Bundles.structureModule Z ⟶ L) :
    (structureModuleIteratedPullbackIso f h).inv ≫
      (Scheme.Modules.pullback h).map ((Scheme.Modules.pullback f).map s) =
        Ample.LineBundles.pullbackSection h (Ample.LineBundles.pullbackSection f s) := by
  simp only [structureModuleIteratedPullbackIso, Iso.trans_inv, Functor.mapIso_inv,
    Ample.LineBundles.pullbackSection, Functor.map_comp, Category.assoc]

/-- Taking regular ratios gives the same result after successive pullbacks and composite pullback. -/
theorem frameCoordinate_pullbackComp (f : Y ⟶ Z) (h : X ⟶ Y) {L : Z.Modules}
    (s t : Line.Bundles.structureModule Z ⟶ L)
    [IsIso (Ample.LineBundles.pullbackSection h (Ample.LineBundles.pullbackSection f s))] [IsIso (Ample.LineBundles.pullbackSection (h ≫ f) s)] :
    Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection (h ≫ f) s) (Ample.LineBundles.pullbackSection (h ≫ f) t) =
      Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection h (Ample.LineBundles.pullbackSection f s)) (Ample.LineBundles.pullbackSection h (Ample.LineBundles.pullbackSection f t)) := by
  have hs : (structureModuleIteratedPullbackIso f h).inv ≫
      (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback h).map s =
      Ample.LineBundles.pullbackSection h (Ample.LineBundles.pullbackSection f s) := section_iteratedPullback f h s
  have ht : (structureModuleIteratedPullbackIso f h).inv ≫
      (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback h).map t =
      Ample.LineBundles.pullbackSection h (Ample.LineBundles.pullbackSection f t) := section_iteratedPullback f h t
  have : IsIso ((structureModuleIteratedPullbackIso f h).inv ≫
      (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback h).map s) := hs.symm ▸ inferInstance
  have : IsIso ((Line.Bundles.structureModulePullbackIso (h ≫ f)).inv ≫ (Scheme.Modules.pullback (h ≫ f)).map s) :=
    inferInstanceAs (IsIso (Ample.LineBundles.pullbackSection (h ≫ f) s))
  have he := Comparison.frameCoordinate_functorComparison
    (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback h) (Scheme.Modules.pullback (h ≫ f))
    (Scheme.Modules.pullbackComp h f) (structureModuleIteratedPullbackIso f h)
    (Line.Bundles.structureModulePullbackIso (h ≫ f)) s t
  exact he.trans (FrameRestriction.frameCoordinate_congr hs ht)

/-- Equal base maps give equal regular ratios of the pulled-back sections. -/
theorem frameCoordinate_pullbackCongr {f h : X ⟶ Y} (he : f = h) {L : Y.Modules}
    (s t : Line.Bundles.structureModule Y ⟶ L) [IsIso (Ample.LineBundles.pullbackSection f s)] [IsIso (Ample.LineBundles.pullbackSection h s)] :
    Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t) =
      Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection h s) (Ample.LineBundles.pullbackSection h t) := by
  subst h
  rfl

/-- A section remains a frame after any map into its nonvanishing open. -/
instance pullbackSection_through_nonvanishing_isIso {L : Y.Modules}
    (s : Line.Bundles.structureModule Y ⟶ L) (h : X ⟶ (Ample.LineBundles.sectionNonvanishing s).toScheme) :
    IsIso (Ample.LineBundles.pullbackSection (h ≫ (Ample.LineBundles.sectionNonvanishing s).ι) s) :=
  (Section.Nonvanishing.isIso_pullbackSection_comp_iff (Ample.LineBundles.sectionNonvanishing s).ι h s).mp inferInstance

/-- Restricting the canonical section ratio to an open part of the nonvanishing open
is the ratio of the sections pulled directly to that open. -/
theorem sectionRatio_restrict {L : Y.Modules} (s t : Line.Bundles.structureModule Y ⟶ L)
    (h : X ⟶ (Ample.LineBundles.sectionNonvanishing s).toScheme) [IsOpenImmersion h] :
    h.appTop (Section.Frames.sectionRatio s t) = Coordinates.frameCoordinate
      (Ample.LineBundles.pullbackSection (h ≫ (Ample.LineBundles.sectionNonvanishing s).ι) s)
      (Ample.LineBundles.pullbackSection (h ≫ (Ample.LineBundles.sectionNonvanishing s).ι) t) := by
  exact (congrArg (fun a => h.appTop a) (Coordinates.sectionRatio_eq_frameCoordinate s t)).trans
    ((FrameRestriction.frameCoordinate_pullback h (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι s)
      (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι t)).symm.trans
        (frameCoordinate_pullbackComp (Ample.LineBundles.sectionNonvanishing s).ι h s t).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.PullbackCoherence
