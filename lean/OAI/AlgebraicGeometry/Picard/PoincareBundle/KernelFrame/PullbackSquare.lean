import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationPullbackSquare
import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.CoordinateMap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.FixedMap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesPullback

/-! # Pullback Square -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.PullbackSquare

noncomputable section

/-! The actual kernel-frame system pulls through both coordinate maps with its full inverse-image kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationPullbackSquare

variable {S : Scheme.{u}} {E F A B C X Y : Over S} [GrpObj A] [GrpObj B] [GrpObj C]
  (p : E ⟶ A) (r : E ⟶ X) (p' : F ⟶ B) (r' : F ⟶ Y)
  (q : E ⟶ F) (f : A ⟶ B) [IsMonHom f] (g : X ⟶ Y)
  (hp : q ≫ p' = p ≫ f) (hr : q ≫ r' = r ≫ g)
  (L : Line.Bundles.LineBundle F.left) (D : FiberwiseMultiplication.Multiplication p' r' L)
  (m : B ⟶ C) [IsMonHom m] (K : FiberwiseMultiplication.KernelFrames p' r' L m D)

/-- The complete pulled frame system first lies over the original image coordinates. -/
def imageFrames : FiberwiseMultiplication.KernelFrames (p ≫ f) (r ≫ g) (L.pullback q.left) m
    (MultiplicationPullbackSquare.imageMultiplication p r p' r' q f g hp hr L D) :=
  Kernel.FramesPullback.congrCoordinates m (L.pullback q.left)
    (FiberwiseMultiplicationPullback.pullbackMultiplication p' r' q L D)
    (Kernel.FramesPullback.pullbackFrames p' r' q m L D K) hp hr

/-- Restricting both coordinates gives genuine frames on the scheme-theoretic inverse-image kernel. -/
def frames : FiberwiseMultiplication.KernelFrames p r (L.pullback q.left) (f ≫ m)
    (MultiplicationPullbackSquare.multiplication p r p' r' q f g hp hr L D) :=
  FixedMap.restrictFixed p r g (f ≫ m) (L.pullback q.left)
    (MultiplicationCoordinateMap.restrictCoordinate p (r ≫ g) f (L.pullback q.left)
      (MultiplicationPullbackSquare.imageMultiplication p r p' r' q f g hp hr L D))
    (CoordinateMap.restrictCoordinate p (r ≫ g) f m (L.pullback q.left)
      (MultiplicationPullbackSquare.imageMultiplication p r p' r' q f g hp hr L D)
      (imageFrames p r p' r' q f g hp hr L D m K))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.PullbackSquare
