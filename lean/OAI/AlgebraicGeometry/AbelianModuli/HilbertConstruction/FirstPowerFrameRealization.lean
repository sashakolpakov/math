import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.FrameRecognition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReindexedOpenFrameTransitions

/-! # First Power Frame Realization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Taking the first power of a transition cocycle preserves its actual frame realization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M : X.Modules} (E : CompatibleSheaf.CompatibleSheafFrames D M)

def CompatibleSheaf.CompatibleSheafFrames.firstPower : CompatibleSheaf.CompatibleSheafFrames (D.power 1) M where
  frame := E.frame
  restrict := E.restrict
  change V i j hi hj x := by
    change E.frame V i hi ((D.value V i j hi hj ^ 1).val * x) = E.frame V j hj x
    rw [pow_one]
    exact E.change V i j hi hj x

def FirstPowerFrameRealization.openFramePowerOneIso {κ : Type u} {V : κ → X.Opens} (C : OpenFrame.Transitions.OpenFrameTransitions V)
    (hV : ∀ x : X, ∃ i, x ∈ V i) : OpenFrame.ModuleSheaf.openFrameModuleSheaf (C.power 1) ≅ OpenFrame.ModuleSheaf.openFrameModuleSheaf C :=
  Sheaf.FrameRecognition.openFrameSheafRecognitionIso (C.power 1) (ConstructedCompatibleFrames.openFrameSheafFrames C).firstPower hV

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
