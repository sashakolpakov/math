import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.SquareValues
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

/-! # Exchanged Kernel Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ExchangedKernelFrames

noncomputable section

/-! Exchanging the two actual line-family coordinates exchanges kernel frames and preserves isotropy. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

variable {S : Scheme.{u}} {A B X Y : Over S} [GrpObj A] [GrpObj B] [GrpObj X] [GrpObj Y]
  (f : A ⟶ B) [IsMonHom f] (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)

/-- The second product becomes the first product on the actual exchanged line. -/
def horizontal := MultiplicationCoordinates.congrCoordinates
  (FiberwiseMultiplicationPullback.pullbackMultiplication (snd A X) (fst A X) (β_ X A).hom L Dv)
  (braiding_hom_snd X A) (braiding_hom_fst X A)

/-- The first product becomes the second product on the actual exchanged line. -/
def vertical := MultiplicationCoordinates.congrCoordinates
  (FiberwiseMultiplicationPullback.pullbackMultiplication (fst A X) (snd A X) (β_ X A).hom L Dh)
  (braiding_hom_fst X A) (braiding_hom_snd X A)

variable (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh)
  (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- The old second kernel gives the first actual frame system after coordinate exchange. -/
def firstFrames : FiberwiseMultiplication.KernelFrames (fst X A) (snd X A) (L.pullback (β_ X A).hom.left) g (horizontal L Dv) :=
  Kernel.FramesPullback.congrCoordinates g (L.pullback (β_ X A).hom.left)
    (FiberwiseMultiplicationPullback.pullbackMultiplication (snd A X) (fst A X) (β_ X A).hom L Dv)
    (Kernel.FramesPullback.pullbackFrames (snd A X) (fst A X) (β_ X A).hom g L Dv Kv)
    (braiding_hom_snd X A) (braiding_hom_fst X A)

/-- The old first kernel gives the second actual frame system after coordinate exchange. -/
def secondFrames : FiberwiseMultiplication.KernelFrames (snd X A) (fst X A) (L.pullback (β_ X A).hom.left) f (vertical L Dh) :=
  Kernel.FramesPullback.congrCoordinates f (L.pullback (β_ X A).hom.left)
    (FiberwiseMultiplicationPullback.pullbackMultiplication (fst A X) (snd A X) (β_ X A).hom L Dh)
    (Kernel.FramesPullback.pullbackFrames (fst A X) (snd A X) (β_ X A).hom f L Dh Kh)
    (braiding_hom_fst X A) (braiding_hom_snd X A)

/-- The first exchanged frames retain the complete transverse product law. -/
theorem first_transverse (ht : Kernel.FramesTransverseTransport.Transverse g Kv Dh) :
    Kernel.FramesTransverseTransport.Transverse g (firstFrames g L Dv Kv) (vertical L Dh) := by
  apply Kernel.FramesTransverseTransport.congrCoordinates
  exact Kernel.FramesTransverseTransport.pullback g (β_ X A).hom Kv Dh ht

/-- The second exchanged frames retain the complete transverse product law. -/
theorem second_transverse (ht : Kernel.FramesTransverseTransport.Transverse f Kh Dv) :
    Kernel.FramesTransverseTransport.Transverse f (secondFrames f L Dh Kh) (horizontal L Dv) := by
  apply Kernel.FramesTransverseTransport.congrCoordinates
  exact Kernel.FramesTransverseTransport.pullback f (β_ X A).hom Kh Dv ht

/-- Coordinate exchange preserves vanishing of the actual frame-ratio obstruction on all test schemes. -/
theorem isotropic (hi : Biextension.Compatibility.Isotropic L Dh Dv f g Kh Kv) :
    Biextension.Compatibility.Isotropic (L.pullback (β_ X A).hom.left)
      (horizontal L Dv) (vertical L Dh) g f (firstFrames g L Dv Kv) (secondFrames f L Dh Kh) := by
  intro T y x a hy hx
  have hx' : x ≫ Kernel.Scheme.kernelInclusion f = (a ≫ (β_ X A).hom) ≫ fst A X := by simp [hx]
  have hy' : y ≫ Kernel.Scheme.kernelInclusion g = (a ≫ (β_ X A).hom) ≫ snd A X := by simp [hy]
  have h := (Line.FrameUnits.frameRatio_eq_one_iff _ _).mp (hi T x y (a ≫ (β_ X A).hom) hx' hy')
  apply (Line.FrameUnits.frameRatio_eq_one_iff _ _).mpr
  unfold firstFrames secondFrames
  rw [KernelFrame.SquareValues.congrCoordinates_frame _ _ _ _ _ _ y a hy
      (by simpa only [Category.assoc] using hy'),
    KernelFrame.SquareValues.congrCoordinates_frame _ _ _ _ _ _ x a hx
      (by simpa only [Category.assoc] using hx')]
  exact congrArg (Pulled.LineSection.transportFrame (β_ X A).hom L a (a ≫ (β_ X A).hom) rfl) h.symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ExchangedKernelFrames
