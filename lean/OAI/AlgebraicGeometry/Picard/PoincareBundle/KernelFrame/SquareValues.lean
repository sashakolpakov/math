import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.PullbackSquare

/-! # Square Values -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.SquareValues

noncomputable section

/-! Evaluation of the complete kernel-frame pullback is the actual transported target frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {S : Scheme.{u}} {E A B X : Over S} [GrpObj A] [GrpObj B]
  {p p' : E ⟶ A} {r r' : E ⟶ X} (f : A ⟶ B) [IsMonHom f]
  (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication p r L) (K : FiberwiseMultiplication.KernelFrames p r L f D)
  (hp : p = p') (hr : r = r')

/-- Coordinate equalities do not alter the actual frame isomorphism. -/
theorem congrCoordinates_frame {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ E)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ p') (hb : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ p) :
    (Kernel.FramesPullback.congrCoordinates f L D K hp hr).frame k a ha = K.frame k a hb := by
  cases hp
  cases hr
  rfl

variable {F C Y : Over S} [GrpObj C]
  (s : E ⟶ A) (t : E ⟶ X) (s' : F ⟶ B) (t' : F ⟶ Y)
  (q : E ⟶ F) (g : X ⟶ Y)
  (hs : q ≫ s' = s ≫ f) (ht : q ≫ t' = t ≫ g)
  (M : Line.Bundles.LineBundle F.left) (D' : FiberwiseMultiplication.Multiplication s' t' M)
  (m : B ⟶ C) [IsMonHom m] (K' : FiberwiseMultiplication.KernelFrames s' t' M m D')

/-- The represented inverse-image kernel frame is exactly the original target frame through fiber pullback. -/
theorem frames_frame {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject (f ≫ m)) (a : T ⟶ E)
    (ha : k ≫ Kernel.Scheme.kernelInclusion (f ≫ m) = a ≫ s)
    (hb : (k ≫ Kernel.PreimageQuotient.map f m) ≫ Kernel.Scheme.kernelInclusion m = (a ≫ q) ≫ s') :
    (PullbackSquare.frames s t s' t' q f g hs ht M D' m K').frame k a ha =
      Pulled.LineSection.transportFrame q M a (a ≫ q) rfl
        (K'.frame (k ≫ Kernel.PreimageQuotient.map f m) (a ≫ q) hb) := by
  unfold PullbackSquare.frames FixedMap.restrictFixed
    CoordinateMap.restrictCoordinate
  dsimp only
  unfold PullbackSquare.imageFrames
  rw [congrCoordinates_frame m (M.pullback q.left)
    (FiberwiseMultiplicationPullback.pullbackMultiplication s' t' q M D')
    (Kernel.FramesPullback.pullbackFrames s' t' q m M D' K') hs ht _ a _
    (by simpa only [Category.assoc] using hb)]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.SquareValues
