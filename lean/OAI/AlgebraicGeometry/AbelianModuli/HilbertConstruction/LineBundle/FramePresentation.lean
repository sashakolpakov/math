import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.IsoValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.FrameRecognition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FromOpenFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InverseFrameTransitions

/-! # Frame Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every actual line bundle is recovered from the transition cocycle of its chosen local trivializations. The reciprocal cocycle also constructs an actual line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)

def Line.Bundles.LineBundle.frameOpen (x : X) : X.Opens := (L.locallyTrivial x).choose

theorem Line.Bundles.LineBundle.mem_frameOpen (x : X) : x ∈ L.frameOpen x := (L.locallyTrivial x).choose_spec.1

def Line.Bundles.LineBundle.chosenFrame (x : X) :
    (Scheme.Modules.pullback (L.frameOpen x).ι).obj L.sheaf ≅ Line.Bundles.structureModule (L.frameOpen x).toScheme :=
  Classical.choice (L.locallyTrivial x).choose_spec.2

def Line.Bundles.LineBundle.chosenRestrictionFrame (x : X) :
    (Line.Bundles.structureModule X).restrict (L.frameOpen x).ι ≅ L.sheaf.restrict (L.frameOpen x).ι :=
  (Scheme.Modules.restrictFunctorIsoPullback (L.frameOpen x).ι).app (Line.Bundles.structureModule X) ≪≫
    Line.Bundles.structureModulePullbackIso (L.frameOpen x).ι ≪≫ (L.chosenFrame x).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback (L.frameOpen x).ι).symm.app L.sheaf

def Line.Bundles.LineBundle.naturalFrames : NaturalSheaf.NaturalSheafFrames L.frameOpen L.sheaf where
  frame V x h := OpenModule.IsoValues.openModuleIsoValue (L.frameOpen x).ι (L.chosenRestrictionFrame x) V
    (by simpa only [Scheme.Opens.opensRange_ι] using h)
  restrict V W h x hx r :=
    (OpenModule.MapValues.openModuleMapValue_natural (L.frameOpen x).ι (L.chosenRestrictionFrame x).hom h
      (by simpa only [Scheme.Opens.opensRange_ι] using hx)
      (by simpa only [Scheme.Opens.opensRange_ι] using h.trans hx) r).symm

theorem Line.Bundles.LineBundle.frameOpen_covers (x : X) : ∃ i, x ∈ L.frameOpen i := ⟨x, L.mem_frameOpen x⟩

def Line.Bundles.LineBundle.framePresentationIso :
    (LineBundle.FromOpenFrames.lineBundleFromOpenFrames L.naturalFrames.transitions L.frameOpen_covers).sheaf ≅ L.sheaf :=
  Sheaf.FrameRecognition.openFrameSheafRecognitionIso L.naturalFrames.transitions L.naturalFrames.compatible L.frameOpen_covers

def Line.Bundles.LineBundle.reciprocalFrameBundle : Line.Bundles.LineBundle X :=
  LineBundle.FromOpenFrames.lineBundleFromOpenFrames L.naturalFrames.transitions.reciprocal L.frameOpen_covers

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
