import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FramePresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReciprocalPairingNondegeneracy

/-! # Section Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The constructed inverse line bundle gives a nondegenerate pairing that detects the original line bundle's actual global sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)

def Line.Bundles.LineBundle.sectionPairing : Bilinear.Sheaves.SheafBilinearMap L.sheaf L.reciprocalFrameBundle.sheaf (Line.Bundles.structureModule X) :=
  L.naturalFrames.compatible.reciprocalPairing
    (ConstructedCompatibleFrames.openFrameSheafFrames L.naturalFrames.transitions.reciprocal) L.frameOpen_covers

theorem Line.Bundles.LineBundle.sectionPairing_contractLeft_injective : Function.Injective L.sectionPairing.contractLeft :=
  L.naturalFrames.compatible.reciprocalPairing_contractLeft_injective
    (ConstructedCompatibleFrames.openFrameSheafFrames L.naturalFrames.transitions.reciprocal) L.frameOpen_covers

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
