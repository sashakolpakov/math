import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FramePresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReciprocalFrameTensorIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles

/-! # Tensor Inverse -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The line bundle constructed from reciprocal transitions is an actual tensor inverse. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)

def Line.Bundles.LineBundle.tensorReciprocalFrameIso : (L.tensor L.reciprocalFrameBundle).sheaf ≅ Line.Bundles.structureModule X :=
  L.naturalFrames.compatible.reciprocalTensorIso
    (ConstructedCompatibleFrames.openFrameSheafFrames L.naturalFrames.transitions.reciprocal) L.frameOpen_covers

def Line.Bundles.LineBundle.reciprocalFrameTensorIso : (L.reciprocalFrameBundle.tensor L).sheaf ≅ Line.Bundles.structureModule X :=
  Tensor.ProductSheaf.tensorModuleCommIso L.reciprocalFrameBundle.sheaf L.sheaf ≪≫ L.tensorReciprocalFrameIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
