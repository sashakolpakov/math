import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionScalars

/-! # Frame Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.FrameRestriction

noncomputable section

/-! Regular coordinates in frames commute with restriction to open subschemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L M : X.Modules}

theorem frameCoordinate_congr {s s' t t' : Line.Bundles.structureModule X ⟶ L} [IsIso s] [IsIso s']
    (hs : s = s') (ht : t = t') : Coordinates.frameCoordinate s t = Coordinates.frameCoordinate s' t' := by
  subst s'
  subst t'
  rfl

/-- Changing the target sheaf by an isomorphism preserves the coordinate in a frame. -/
theorem frameCoordinate_targetIso (s t : Line.Bundles.structureModule X ⟶ L) [IsIso s] (h : L ≅ M) :
    Coordinates.frameCoordinate (s ≫ h.hom) (t ≫ h.hom) = Coordinates.frameCoordinate s t := by
  have he : Coordinates.frameCoordinateEnd (s ≫ h.hom) (t ≫ h.hom) = Coordinates.frameCoordinateEnd s t := by
    apply (cancel_mono (s ≫ h.hom)).mp
    rw [Coordinates.frameCoordinateEnd_frame]
    simp only [Coordinates.frameCoordinateEnd, Category.assoc, IsIso.inv_hom_id_assoc]
  exact congrArg (Coordinates.structureModuleEndValue X) he

/-- Restriction in any chosen frame of the restricted structure module gives the usual
restriction of the regular coordinate. -/
theorem frameCoordinate_restrict (f : X ⟶ Y) [IsOpenImmersion f] {L : Y.Modules}
    (s t : Line.Bundles.structureModule Y ⟶ L) [IsIso s]
    (e : (Line.Bundles.structureModule Y).restrict f ≅ Line.Bundles.structureModule X) :
    Coordinates.frameCoordinate (e.inv ≫ (Scheme.Modules.restrictFunctor f).map s)
      (e.inv ≫ (Scheme.Modules.restrictFunctor f).map t) = f.appTop (Coordinates.frameCoordinate s t) := by
  have he : Coordinates.frameCoordinateEnd (e.inv ≫ (Scheme.Modules.restrictFunctor f).map s)
      (e.inv ≫ (Scheme.Modules.restrictFunctor f).map t) =
      e.inv ≫ (Scheme.Modules.restrictFunctor f).map (Coordinates.frameCoordinateEnd s t) ≫ e.hom := by
    apply (cancel_mono (e.inv ≫ (Scheme.Modules.restrictFunctor f).map s)).mp
    rw [Coordinates.frameCoordinateEnd_frame]
    simp only [Coordinates.frameCoordinateEnd, Category.assoc, Iso.hom_inv_id_assoc,
      ← Functor.map_comp, IsIso.inv_hom_id, Category.comp_id]
  exact (congrArg (Coordinates.structureModuleEndValue X) he).trans
    (RestrictionScalars.structureModuleEndValue_restrict f (Coordinates.frameCoordinateEnd s t) e)

/-- Restriction and the canonical pullback give the same section after their module comparisons. -/
theorem section_restrict_to_pullback (f : X ⟶ Y) [IsOpenImmersion f] {L : Y.Modules}
    (s : Line.Bundles.structureModule Y ⟶ L) :
    (((Scheme.Modules.restrictFunctorIsoPullback f).app (Line.Bundles.structureModule Y) ≪≫
        Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.restrictFunctor f).map s) ≫
      ((Scheme.Modules.restrictFunctorIsoPullback f).app L).hom = Ample.LineBundles.pullbackSection f s := by
  change ((Line.Bundles.structureModulePullbackIso f).inv ≫
      ((Scheme.Modules.restrictFunctorIsoPullback f).app (Line.Bundles.structureModule Y)).inv ≫
        (Scheme.Modules.restrictFunctor f).map s) ≫
      ((Scheme.Modules.restrictFunctorIsoPullback f).app L).hom = _
  simp only [Category.assoc]
  have hn : (Scheme.Modules.restrictFunctor f).map s ≫
      ((Scheme.Modules.restrictFunctorIsoPullback f).app L).hom =
      ((Scheme.Modules.restrictFunctorIsoPullback f).app (Line.Bundles.structureModule Y)).hom ≫
        (Scheme.Modules.pullback f).map s := (Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality s
  exact (congrArg (fun z : (Line.Bundles.structureModule Y).restrict f ⟶ (Scheme.Modules.pullback f).obj L =>
      (Line.Bundles.structureModulePullbackIso f).inv ≫
        ((Scheme.Modules.restrictFunctorIsoPullback f).app (Line.Bundles.structureModule Y)).inv ≫ z) hn).trans
    (by simp only [Iso.inv_hom_id_assoc, Ample.LineBundles.pullbackSection])

/-- Regular frame coordinates pull back as regular functions on open subschemes. -/
theorem frameCoordinate_pullback (f : X ⟶ Y) [IsOpenImmersion f] {L : Y.Modules}
    (s t : Line.Bundles.structureModule Y ⟶ L) [IsIso s] :
    Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t) = f.appTop (Coordinates.frameCoordinate s t) := by
  let e := (Scheme.Modules.restrictFunctorIsoPullback f).app (Line.Bundles.structureModule Y) ≪≫
    Line.Bundles.structureModulePullbackIso f
  have he := frameCoordinate_targetIso (e.inv ≫ (Scheme.Modules.restrictFunctor f).map s)
    (e.inv ≫ (Scheme.Modules.restrictFunctor f).map t) ((Scheme.Modules.restrictFunctorIsoPullback f).app L)
  have hs : (e.inv ≫ (Scheme.Modules.restrictFunctor f).map s) ≫
      ((Scheme.Modules.restrictFunctorIsoPullback f).app L).hom = Ample.LineBundles.pullbackSection f s :=
    section_restrict_to_pullback f s
  have ht : (e.inv ≫ (Scheme.Modules.restrictFunctor f).map t) ≫
      ((Scheme.Modules.restrictFunctorIsoPullback f).app L).hom = Ample.LineBundles.pullbackSection f t :=
    section_restrict_to_pullback f t
  exact (frameCoordinate_congr hs ht).symm.trans (he.trans (frameCoordinate_restrict f s t e))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.FrameRestriction
