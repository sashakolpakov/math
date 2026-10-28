import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.FrameOverComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.FrameTransitionPullback

/-! # Frame Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.FrameTransitions

noncomputable section

/-! Local restrictions of a global frame have literal transition unit one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} {M : X.Modules}

def localFrameOfGlobal (e : M ≅ HilbertConstruction.Line.Bundles.structureModule X) (U : X.Opens) : LineFrameAtlas.LocalLineFrame M :=
  ⟨U, FrameOverComparison.globalOpenFrame e U⟩

theorem localFrameOfGlobal_transition (e : M ≅ HilbertConstruction.Line.Bundles.structureModule X) (U V W : X.Opens)
    (hU : W ≤ U) (hV : W ≤ V) :
    (localFrameOfGlobal e U).transition (localFrameOfGlobal e V) W hU hV = 1 := by
  have h₁ := LineFrameAtlas.LocalLineFrame.transition_native M (localFrameOfGlobal e U) (localFrameOfGlobal e V) W hU hV
  have h₂ := congrArg₂ (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M W)
    (FrameOverComparison.globalOpenFrame_restrict e hU) (FrameOverComparison.globalOpenFrame_restrict e hV)
  exact h₁.trans (h₂.trans (Open.FrameTransitionPullback.nativeOpenFrameTransition_self M W (FrameOverComparison.globalOpenFrame e W)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.FrameTransitions
