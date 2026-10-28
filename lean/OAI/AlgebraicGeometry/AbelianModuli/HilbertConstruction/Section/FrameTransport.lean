import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Comparison

/-! # Frame Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FrameTransport

noncomputable section

/-!
Transport sections through source and target frames, including after arbitrary
scheme pullback. Ratios are unchanged by this simultaneous transport.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {L M : Y.Modules}

/-- Pull an automorphism of the structure module back using the canonical unit comparison. -/
def pullbackStructureAutomorphism (a : Line.Bundles.structureModule Y ≅ Line.Bundles.structureModule Y) :
    Line.Bundles.structureModule X ≅ Line.Bundles.structureModule X :=
  (Line.Bundles.structureModulePullbackIso f).symm ≪≫ (Scheme.Modules.pullback f).mapIso a ≪≫
    Line.Bundles.structureModulePullbackIso f

/-- Pulling back a section transported through frames transports the pulled-back section. -/
theorem pullbackSection_frameTransport (a : Line.Bundles.structureModule Y ≅ Line.Bundles.structureModule Y)
    (e : L ≅ M) (s : Line.Bundles.structureModule Y ⟶ L) :
    Ample.LineBundles.pullbackSection f (a.hom ≫ s ≫ e.hom) =
      (pullbackStructureAutomorphism f a).hom ≫ Ample.LineBundles.pullbackSection f s ≫
        ((Scheme.Modules.pullback f).mapIso e).hom := by
  change (Line.Bundles.structureModulePullbackIso f).inv ≫
      (Scheme.Modules.pullback f).map (a.hom ≫ s ≫ e.hom) =
    ((Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map a.hom ≫
      (Line.Bundles.structureModulePullbackIso f).hom) ≫
      ((Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map s) ≫
        (Scheme.Modules.pullback f).map e.hom
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

theorem pullbackSection_frameTransport_isIso (a : Line.Bundles.structureModule Y ≅ Line.Bundles.structureModule Y)
    (e : L ≅ M) (s : Line.Bundles.structureModule Y ⟶ L) [IsIso (Ample.LineBundles.pullbackSection f s)] :
    IsIso (Ample.LineBundles.pullbackSection f (a.hom ≫ s ≫ e.hom)) := by
  rw [pullbackSection_frameTransport]
  infer_instance

/-- Source-frame and target-frame transport preserve local ratios. -/
theorem frameCoordinate_pullback_frameTransport (a : Line.Bundles.structureModule Y ≅ Line.Bundles.structureModule Y)
    (e : L ≅ M) (s t : Line.Bundles.structureModule Y ⟶ L) [IsIso (Ample.LineBundles.pullbackSection f s)] :
    letI := pullbackSection_frameTransport_isIso f a e s
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f (a.hom ≫ s ≫ e.hom))
      (Ample.LineBundles.pullbackSection f (a.hom ≫ t ≫ e.hom)) =
        Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t) := by
  have hs := pullbackSection_frameTransport f a e s
  have ht := pullbackSection_frameTransport f a e t
  have hsi := pullbackSection_frameTransport_isIso f a e s
  have hc := @Frame.FrameRestriction.frameCoordinate_congr X ((Scheme.Modules.pullback f).obj M)
    _ _ _ _ hsi inferInstance hs ht
  exact hc.trans
    ((Frame.FrameRestriction.frameCoordinate_targetIso ((pullbackStructureAutomorphism f a).hom ≫ Ample.LineBundles.pullbackSection f s)
      ((pullbackStructureAutomorphism f a).hom ≫ Ample.LineBundles.pullbackSection f t)
      ((Scheme.Modules.pullback f).mapIso e)).trans
        (Frame.Comparison.frameCoordinate_sourceIso (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t)
          (pullbackStructureAutomorphism f a)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FrameTransport
