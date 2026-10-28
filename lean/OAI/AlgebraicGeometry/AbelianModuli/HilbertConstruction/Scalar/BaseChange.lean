import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackUnits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.BaseChange

noncomputable section

/-! Regular scalar and frame coordinates commute with arbitrary scheme pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem structureModuleEndValue_baseChange (f : X ⟶ Y) (a : End (Line.Bundles.structureModule Y)) :
    Frame.Coordinates.structureModuleEndValue X ((Line.Bundles.structureModulePullbackIso f).inv ≫
      (Scheme.Modules.pullback f).map a ≫ (Line.Bundles.structureModulePullbackIso f).hom) =
      f.appTop (Frame.Coordinates.structureModuleEndValue Y a) := by
  let e := Line.Bundles.structureModulePullbackIso f
  let b : End (Line.Bundles.structureModule X) := e.inv ≫ (Scheme.Modules.pullback f).map a ≫ e.hom
  have hb : e.hom ≫ b = (Scheme.Modules.pullback f).map a ≫ e.hom := by
    simp only [b, Iso.hom_inv_id_assoc]
  let v : Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X) :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (Line.Bundles.structureModule Y) ≫
      (Scheme.Modules.pushforward f).map e.hom = v := Tensor.PullbackUnits.structureModulePullbackIso_unit f
  have hn : a ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (Line.Bundles.structureModule Y) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (Line.Bundles.structureModule Y) ≫
        (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map a) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a
  have h : v ≫ (Scheme.Modules.pushforward f).map b = a ≫ v := by
    rw [← hu, Category.assoc, ← Functor.map_comp, hb, Functor.map_comp, ← Category.assoc,
      ← hn, Category.assoc]
  have hv := congrArg (fun c : Line.Bundles.structureModule Y ⟶
    (Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X) => c.app ⊤ (1 : Γ(Y, ⊤))) h
  change b.app ⊤ (f.appTop (1 : Γ(Y, ⊤))) = f.appTop (a.app ⊤ (1 : Γ(Y, ⊤))) at hv
  rw [show f.appTop (1 : Γ(Y, ⊤)) = 1 from map_one (f.appTop).hom] at hv
  exact hv

theorem frameCoordinate_baseChange (f : X ⟶ Y) {L : Y.Modules}
    (s t : Line.Bundles.structureModule Y ⟶ L) [IsIso s] :
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t) =
      f.appTop (Frame.Coordinates.frameCoordinate s t) := by
  let e := Line.Bundles.structureModulePullbackIso f
  have he : Frame.Coordinates.frameCoordinateEnd (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t) =
      e.inv ≫ (Scheme.Modules.pullback f).map (Frame.Coordinates.frameCoordinateEnd s t) ≫ e.hom := by
    apply (cancel_mono (Ample.LineBundles.pullbackSection f s)).mp
    rw [Frame.Coordinates.frameCoordinateEnd_frame]
    simp only [Frame.Coordinates.frameCoordinateEnd, Ample.LineBundles.pullbackSection, e, Category.assoc,
      Iso.hom_inv_id_assoc, ← Functor.map_comp, IsIso.inv_hom_id, Category.comp_id]
  exact (congrArg (Frame.Coordinates.structureModuleEndValue X) he).trans
    (structureModuleEndValue_baseChange f (Frame.Coordinates.frameCoordinateEnd s t))

theorem sectionNonvanishing_baseChange_of_frame (f : X ⟶ Y) {L : Y.Modules}
    (s t : Line.Bundles.structureModule Y ⟶ L) [IsIso s] :
    Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f t) = f ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing t := by
  rw [Nonvanishing.sectionNonvanishing_frameCoordinate (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t),
    frameCoordinate_baseChange, ← f.preimage_basicOpen_top,
    Nonvanishing.sectionNonvanishing_frameCoordinate s t]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.BaseChange
