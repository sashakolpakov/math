import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions

/-! # Inverse Frame Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Inverting the actual transition units gives the cocycle of the inverse line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} (D : OpenFrame.Transitions.OpenFrameTransitions U)

def OpenFrame.Transitions.OpenFrameTransitions.reciprocal : OpenFrame.Transitions.OpenFrameTransitions U where
  value V i j hi hj := D.value V j i hj hi
  restrict V W h i j hi hj := D.restrict V W h j i hj hi
  self := D.self
  comp V i j k hi hj hk :=
    (mul_comm _ _).trans (D.comp V k j i hk hj hi)

theorem OpenFrame.Transitions.OpenFrameTransitions.reciprocal_value (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) :
    D.reciprocal.value V i j hi hj = (D.value V i j hi hj)⁻¹ :=
  (D.inverse V i j hi hj).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
