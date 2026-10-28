import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.FrameRestriction
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnitPullbackScalars

/-! # Coordinate Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.CoordinatePullback

noncomputable section

/-! Coordinates of sections in a frame commute with arbitrary pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.FrameRestriction OAI.AlgebraicGeometry.Picard.Homomorphisms.UnitPullbackScalars.Construction

universe u
variable {X Y : Scheme.{u}}

theorem frameCoordinate_pullback_any (f : X ⟶ Y) {L : Y.Modules}
    (s t : HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) [IsIso s] :
    HilbertConstruction.Frame.Coordinates.frameCoordinate (HilbertConstruction.Ample.LineBundles.pullbackSection f s) (HilbertConstruction.Ample.LineBundles.pullbackSection f t) =
      f.appTop (HilbertConstruction.Frame.Coordinates.frameCoordinate s t) := by
  have he : HilbertConstruction.Frame.Coordinates.frameCoordinateEnd (HilbertConstruction.Ample.LineBundles.pullbackSection f s) (HilbertConstruction.Ample.LineBundles.pullbackSection f t) =
      Picard.Homomorphisms.UnitPullbackScalars.Construction.unitEndPullback f (HilbertConstruction.Frame.Coordinates.frameCoordinateEnd s t) := by
    apply (cancel_mono (HilbertConstruction.Ample.LineBundles.pullbackSection f s)).mp
    rw [HilbertConstruction.Frame.Coordinates.frameCoordinateEnd_frame]
    simp only [HilbertConstruction.Frame.Coordinates.frameCoordinateEnd, Picard.Homomorphisms.UnitPullbackScalars.Construction.unitEndPullback, HilbertConstruction.Ample.LineBundles.pullbackSection, Category.assoc,
      Iso.hom_inv_id_assoc, ← Functor.map_comp, IsIso.inv_hom_id, Category.comp_id]
  exact (congrArg (HilbertConstruction.Frame.Coordinates.structureModuleEndValue X) he).trans
    (Picard.Homomorphisms.UnitPullbackScalars.Construction.unitEndPullback_scalar f (HilbertConstruction.Frame.Coordinates.frameCoordinateEnd s t))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.CoordinatePullback
