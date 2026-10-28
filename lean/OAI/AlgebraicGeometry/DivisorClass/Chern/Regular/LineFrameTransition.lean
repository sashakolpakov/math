import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineSectionFrames
import OAI.AlgebraicGeometry.DivisorClass.Chern.FramesFrame

/-! # Line Frame Transition -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineFrameTransition

noncomputable section

/-! The original Chern-class frame convention extracts the reversed coordinate transition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} {ι : Type} (D : FunctionGluing.RegularLineCocycle X ι)

/-- The original algebraic transition is the coordinate in frame `i` of the
generator of frame `j`, hence the coordinate-change unit from `j` to `i`. -/
theorem regularLineSectionLinearFrame_transition (i j : ι) (W : X.Opens)
    (hi : W ≤ D.domain i) (hj : W ≤ D.domain j) :
    FramesFrame.Construction.frameTransitionUnit (LineSectionFrames.regularLineSectionLinearFrame D i hi)
      (LineSectionFrames.regularLineSectionLinearFrame D j hj) = D.transition j i W hj hi := by
  apply Units.ext
  change (D.transition j i W hj hi : Γ(X, W)) * FunctionGluing.regularRestriction le_rfl 1 =
    (D.transition j i W hj hi : Γ(X, W))
  rw [map_one, mul_one]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineFrameTransition
