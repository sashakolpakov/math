import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.FrameRestriction

/-! # Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Comparison

noncomputable section

/-! Frame coordinates are independent of isomorphic choices in module-sheaf pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L : X.Modules}

/-- Changing the source frame of both sections leaves their ratio unchanged. -/
theorem frameCoordinate_sourceIso (s t : Line.Bundles.structureModule X ⟶ L) [IsIso s]
    (e : Line.Bundles.structureModule X ≅ Line.Bundles.structureModule X) :
    Coordinates.frameCoordinate (e.hom ≫ s) (e.hom ≫ t) = Coordinates.frameCoordinate s t := by
  let a : End (Line.Bundles.structureModule X) := e.hom
  let b : End (Line.Bundles.structureModule X) := e.inv
  have he : Coordinates.frameCoordinateEnd (e.hom ≫ s) (e.hom ≫ t) =
      b * Coordinates.frameCoordinateEnd s t * a := by
    apply (cancel_mono (e.hom ≫ s)).mp
    rw [Coordinates.frameCoordinateEnd_frame]
    change e.hom ≫ t = (e.hom ≫ (t ≫ inv s) ≫ e.inv) ≫ (e.hom ≫ s)
    simp only [Category.assoc, Iso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
  have hba : b * a = 1 := e.hom_inv_id
  have hu : Coordinates.structureModuleEndValue X b * Coordinates.structureModuleEndValue X a = 1 :=
    (map_mul (Coordinates.structureModuleEndValue X) b a).symm.trans
      ((congrArg (Coordinates.structureModuleEndValue X) hba).trans (map_one (Coordinates.structureModuleEndValue X)))
  change Coordinates.structureModuleEndValue X (Coordinates.frameCoordinateEnd _ _) = Coordinates.structureModuleEndValue X (Coordinates.frameCoordinateEnd s t)
  rw [he, map_mul, map_mul, mul_assoc, mul_comm (Coordinates.structureModuleEndValue X (Coordinates.frameCoordinateEnd s t))
    (Coordinates.structureModuleEndValue X a), ← mul_assoc, hu, one_mul]

/-- A natural isomorphism of module functors transports a section, up to the induced source frame. -/
theorem framedSection_functorComparison (F G : Y.Modules ⥤ X.Modules) (e : F ≅ G)
    (uF : F.obj (Line.Bundles.structureModule Y) ≅ Line.Bundles.structureModule X)
    (uG : G.obj (Line.Bundles.structureModule Y) ≅ Line.Bundles.structureModule X)
    {L : Y.Modules} (s : Line.Bundles.structureModule Y ⟶ L) :
    (((uG.symm ≪≫ e.symm.app (Line.Bundles.structureModule Y) ≪≫ uF).hom ≫ (uF.inv ≫ F.map s)) ≫
      (e.app L).hom) = uG.inv ≫ G.map s := by
  change ((uG.inv ≫ (e.app (Line.Bundles.structureModule Y)).inv ≫ uF.hom) ≫
      (uF.inv ≫ F.map s)) ≫ (e.app L).hom = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (congrArg (fun z : F.obj (Line.Bundles.structureModule Y) ⟶ G.obj L =>
    uG.inv ≫ (e.app (Line.Bundles.structureModule Y)).inv ≫ z) (e.hom.naturality s)).trans
      (congrArg (fun z : G.obj (Line.Bundles.structureModule Y) ⟶ G.obj L => uG.inv ≫ z)
        ((e.app (Line.Bundles.structureModule Y)).inv_hom_id_assoc (G.map s)))

/-- Ratios of transported sections are independent of a natural isomorphism between the functors
and the chosen comparisons with the structure module. -/
theorem frameCoordinate_functorComparison (F G : Y.Modules ⥤ X.Modules) (e : F ≅ G)
    (uF : F.obj (Line.Bundles.structureModule Y) ≅ Line.Bundles.structureModule X)
    (uG : G.obj (Line.Bundles.structureModule Y) ≅ Line.Bundles.structureModule X)
    {L : Y.Modules} (s t : Line.Bundles.structureModule Y ⟶ L)
    [IsIso (uF.inv ≫ F.map s)] [IsIso (uG.inv ≫ G.map s)] :
    Coordinates.frameCoordinate (uG.inv ≫ G.map s) (uG.inv ≫ G.map t) =
      Coordinates.frameCoordinate (uF.inv ≫ F.map s) (uF.inv ≫ F.map t) := by
  let a := uG.symm ≪≫ e.symm.app (Line.Bundles.structureModule Y) ≪≫ uF
  have hs := framedSection_functorComparison F G e uF uG s
  have ht := framedSection_functorComparison F G e uF uG t
  exact (FrameRestriction.frameCoordinate_congr hs ht).symm.trans
    ((FrameRestriction.frameCoordinate_targetIso (a.hom ≫ (uF.inv ≫ F.map s))
      (a.hom ≫ (uF.inv ≫ F.map t)) (e.app L)).trans
        (frameCoordinate_sourceIso (uF.inv ≫ F.map s) (uF.inv ≫ F.map t) a))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Comparison
