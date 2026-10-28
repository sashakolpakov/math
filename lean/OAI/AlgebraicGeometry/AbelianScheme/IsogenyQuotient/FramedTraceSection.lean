import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Trace
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedNormSection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormSectionLineIsomorphism

/-! # Framed Trace Section -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedTraceSection.Construction

noncomputable section

/-! Taking the finite trace of the coordinate of an actual section
produces a section downstairs, independently of the line's frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules}

def framedTraceSection (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) [IsIso e]
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L :=
  (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv Y).symm
    (Trace.Construction.schemeTrace f (AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e) z)) ≫ e

theorem framedTraceSection_coordinate (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) [IsIso e]
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L) :
    AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate e (framedTraceSection f e z) =
      Trace.Construction.schemeTrace f (AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e) z) :=
  (AbelianModuli.HilbertConstruction.Framed.AffineExtension.frameCoordinate_scalar_frame e ((AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv Y).symm _)).trans
    ((AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv Y).apply_symm_apply _)

theorem framedTraceSection_frame_independent
    (e e' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) [IsIso e] [IsIso e']
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L) :
    framedTraceSection f e z = framedTraceSection f e' z := by
  apply AbelianModuli.HilbertConstruction.Framed.AffineAnnihilation.frameCoordinate_injective e
  dsimp only
  rw [framedTraceSection_coordinate, AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate_change e e',
    framedTraceSection_coordinate]
  have hc := AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate_change (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e') z
  rw [AbelianModuli.HilbertConstruction.Scalar.BaseChange.frameCoordinate_baseChange] at hc
  rw [hc, Trace.Construction.schemeTrace_scalar]

theorem framedTraceSection_mapIso {M : Y.Modules}
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) [IsIso e] (a : L ≅ M)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L) :
    framedTraceSection f (e ≫ a.hom) (z ≫ (Scheme.Modules.pullback f).map a.hom) =
      framedTraceSection f e z ≫ a.hom := by
  have hc : AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (e ≫ a.hom))
      (z ≫ (Scheme.Modules.pullback f).map a.hom) =
      AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e) z :=
    (AbelianModuli.HilbertConstruction.Frame.FrameRestriction.frameCoordinate_congr (AbelianModuli.HilbertConstruction.Power.SectionTransitions.pullbackSection_postcomp f e a.hom) rfl).trans
      (AbelianModuli.HilbertConstruction.Frame.FrameRestriction.frameCoordinate_targetIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e) z ((Scheme.Modules.pullback f).mapIso a))
  simp only [framedTraceSection, hc, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedTraceSection.Construction
