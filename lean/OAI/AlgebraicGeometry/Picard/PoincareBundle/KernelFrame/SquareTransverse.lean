import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.PullbackSquare
import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.CoordinateTransverse
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationRestrictionCommutes

/-! # Square Transverse -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.SquareTransverse

noncomputable section

/-! The full kernel-frame pullback through both coordinate maps preserves transverse multiplication. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationPullbackSquare OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.PullbackSquare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

variable {S : Scheme.{u}} {E F A B C X Y : Over S}
  [GrpObj A] [GrpObj B] [GrpObj C] [GrpObj X] [GrpObj Y]
  (p : E ⟶ A) (r : E ⟶ X) (p' : F ⟶ B) (r' : F ⟶ Y)
  (q : E ⟶ F) (f : A ⟶ B) [IsMonHom f] (g : X ⟶ Y) [IsMonHom g]
  (hp : q ≫ p' = p ≫ f) (hr : q ≫ r' = r ≫ g)
  (L : Line.Bundles.LineBundle F.left)
  (Dh : FiberwiseMultiplication.Multiplication p' r' L) (Dv : FiberwiseMultiplication.Multiplication r' p' L)
  (m : B ⟶ C) [IsMonHom m] (K : FiberwiseMultiplication.KernelFrames p' r' L m Dh)
  (ht : Kernel.FramesTransverseTransport.Transverse m K Dv)

include ht

/-- The actual pulled inverse-image kernel frames retain their transverse law after both coordinate changes. -/
theorem frames_transverse : Kernel.FramesTransverseTransport.Transverse (f ≫ m)
    (PullbackSquare.frames p r p' r' q f g hp hr L Dh m K)
    (MultiplicationPullbackSquare.multiplication r p r' p' q g f hr hp L Dv) := by
  let Dh0 := MultiplicationPullbackSquare.imageMultiplication p r p' r' q f g hp hr L Dh
  let Dv0 := MultiplicationPullbackSquare.imageMultiplication r p r' p' q g f hr hp L Dv
  let K0 := PullbackSquare.imageFrames p r p' r' q f g hp hr L Dh m K
  have h0 : Kernel.FramesTransverseTransport.Transverse m K0 Dv0 :=
    Kernel.FramesTransverseTransport.congrCoordinates m
      (Kernel.FramesPullback.pullbackFrames p' r' q m L Dh K)
      (FiberwiseMultiplicationPullback.pullbackMultiplication r' p' q L Dv) hp hr
      (Kernel.FramesTransverseTransport.pullback m q K Dv ht)
  let K1 := CoordinateMap.restrictCoordinate p (r ≫ g) f m (L.pullback q.left) Dh0 K0
  have h1 : Kernel.FramesTransverseTransport.Transverse (f ≫ m) K1
      (MultiplicationFixedMap.restrictFixed (r ≫ g) p f (L.pullback q.left) Dv0) :=
    CoordinateTransverse.restrictCoordinate p (r ≫ g) f m (L.pullback q.left) Dh0 Dv0 K0 h0
  have h2 := CoordinateTransverse.restrictFixed p r g (f ≫ m) (L.pullback q.left)
    (MultiplicationCoordinateMap.restrictCoordinate p (r ≫ g) f (L.pullback q.left) Dh0)
    (MultiplicationFixedMap.restrictFixed (r ≫ g) p f (L.pullback q.left) Dv0) K1 h1
  rw [MultiplicationRestrictionCommutes.restrict_commutes] at h2
  exact h2

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.SquareTransverse
