import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationFixedMap

/-! # Fixed Map -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.FixedMap

noncomputable section

/-! Refining the fixed coordinate retains the entire actual kernel-frame system. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {S : Scheme.{u}} {E A B X Y : Over S} [GrpObj A] [GrpObj B]
  (p : E ⟶ A) (r : E ⟶ X) (g : X ⟶ Y) (f : A ⟶ B) [IsMonHom f]
  (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication p (r ≫ g) L)
  (K : FiberwiseMultiplication.KernelFrames p (r ≫ g) L f D)

/-- All kernel-frame laws are inherited from the actual multiplication with the coarser fixed coordinate. -/
def restrictFixed : FiberwiseMultiplication.KernelFrames p r L f (MultiplicationFixedMap.restrictFixed p r g L D) where
  frame := K.frame
  unit := K.unit
  multiplicative := fun {_T} k l t hkt a b c ha hb hc hab U =>
    K.multiplicative k l t hkt a b c ha hb hc (MultiplicationFixedMap.mappedRel p r g a b c hab) U
  natural := K.natural

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.FixedMap
