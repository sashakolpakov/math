import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.CoordinateMap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.FixedMap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

/-! # Coordinate Transverse -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.CoordinateTransverse

noncomputable section

/-! Transverse multiplication survives refinement of either actual coordinate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

section GroupCoordinate

variable {S : Scheme.{u}} {E A B C X : Over S} [GrpObj A] [GrpObj B] [GrpObj C] [GrpObj X]
  (p : E ⟶ A) (r : E ⟶ X) (f : A ⟶ B) [IsMonHom f] (m : B ⟶ C) [IsMonHom m]
  (L : Line.Bundles.LineBundle E.left) (Dh : FiberwiseMultiplication.Multiplication (p ≫ f) r L)
  (Dv : FiberwiseMultiplication.Multiplication r (p ≫ f) L) (K : FiberwiseMultiplication.KernelFrames (p ≫ f) r L m Dh)
  (ht : Kernel.FramesTransverseTransport.Transverse m K Dv)

include ht

/-- The actual inverse-image kernel retains transversality under the group-coordinate map. -/
theorem restrictCoordinate :
    Kernel.FramesTransverseTransport.Transverse (f ≫ m) (CoordinateMap.restrictCoordinate p r f m L Dh K)
      (MultiplicationFixedMap.restrictFixed r p f L Dv) := by
  intro T k a b c ha hb hc h U
  exact ht T (k ≫ Kernel.PreimageQuotient.map f m) a b c
    (CoordinateMap.imageKernel p f m k a ha)
    (CoordinateMap.imageKernel p f m k b hb)
    (CoordinateMap.imageKernel p f m k c hc)
    (MultiplicationFixedMap.mappedRel r p f a b c h) U

end GroupCoordinate

variable {S : Scheme.{u}} {E A B X Y : Over S} [GrpObj A] [GrpObj B] [GrpObj X] [GrpObj Y]
  (p : E ⟶ A) (r : E ⟶ X) (g : X ⟶ Y) [IsMonHom g] (m : A ⟶ B) [IsMonHom m]
  (L : Line.Bundles.LineBundle E.left) (Dh : FiberwiseMultiplication.Multiplication p (r ≫ g) L)
  (Dv : FiberwiseMultiplication.Multiplication (r ≫ g) p L) (K : FiberwiseMultiplication.KernelFrames p (r ≫ g) L m Dh)
  (ht : Kernel.FramesTransverseTransport.Transverse m K Dv)

include ht

/-- Refining the fixed coordinate retains transversality for the genuine group law in that coordinate. -/
theorem restrictFixed :
    Kernel.FramesTransverseTransport.Transverse m (FixedMap.restrictFixed p r g m L Dh K)
      (MultiplicationCoordinateMap.restrictCoordinate r p g L Dv) := by
  intro T k a b c ha hb hc h U
  exact ht T k a b c ha hb hc (MultiplicationCoordinateMap.mappedRel r p g a b c h) U

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.CoordinateTransverse
