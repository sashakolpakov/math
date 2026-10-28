import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GeneratorChanges
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModuleSheaf

/-! # Constructed Compatible Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstructedCompatibleFrames

noncomputable section

/-! The glued frame sheaf has actual compatible local frames realizing its defining cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : OpenFrame.Transitions.OpenFrameTransitions U)

def openFrameSheafFrames : CompatibleSheaf.CompatibleSheafFrames D (OpenFrame.ModuleSheaf.openFrameModuleSheaf D) where
  frame V i hi := OpenFrame.LocalFreeness.openFrameLocalEquiv D V i hi
  restrict V W h i hi x := OpenFrame.GeneratorNaturality.openFrameGenerator_restriction D (V := V) (W := W) h i hi x
  change V i j hi hj x := OpenFrame.GeneratorChanges.openFrameGenerator_change D V i j hi hj x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstructedCompatibleFrames
