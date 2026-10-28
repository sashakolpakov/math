import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

/-! # Transverse Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.TransverseFrames

noncomputable section

/-!
# Actual biextension symmetry constructs the second transverse kernel-frame law
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (L : Line.Bundles.LineBundle (A ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A A) (snd A A) L) (Dv : FiberwiseMultiplication.Multiplication (snd A A) (fst A A) L)
  (symmetry : (Scheme.Modules.pullback (β_ A A).hom.left).obj L.sheaf ≅ L.sheaf)

/-- Exchange the actual second multiplication. -/
def exchangedVertical : FiberwiseMultiplication.Multiplication (fst A A) (snd A A) (L.pullback (β_ A A).hom.left) :=
  MultiplicationCoordinates.congrCoordinates
    (FiberwiseMultiplicationPullback.pullbackMultiplication (snd A A) (fst A A) (β_ A A).hom L Dv)
    (braiding_hom_snd A A) (braiding_hom_fst A A)

/-- Transport the exchanged second product back to the original line. -/
def returnedFirst : FiberwiseMultiplication.Multiplication (fst A A) (snd A A) L :=
  FiberwiseMultiplicationIso.transportMultiplication (fst A A) (snd A A)
    (L.pullback (β_ A A).hom.left) L symmetry (exchangedVertical L Dv)

variable (f : A ⟶ B) [IsMonHom f] (F : FiberwiseMultiplication.KernelFrames (fst A A) (snd A A) L f Dh)

/-- Symmetry transfers the first transverse law to the constructed second frame system. -/
theorem second_transverse (ht : Kernel.FramesTransverseTransport.Transverse f F Dv) :
    Kernel.FramesTransverseTransport.Transverse f (MultiplicativeFrames.secondFrames L Dh symmetry f F) (returnedFirst L Dv symmetry) := by
  apply Kernel.FramesTransverseTransport.iso
  apply Kernel.FramesTransverseTransport.congrCoordinates
  exact Kernel.FramesTransverseTransport.pullback f (β_ A A).hom F Dv ht

/-- Equality with the actual second product identifies the constructed full frame system with that product. -/
def secondFramesOfCompatible (hv : MultiplicativeFrames.secondMultiplication L Dh symmetry = Dv) :
    FiberwiseMultiplication.KernelFrames (snd A A) (fst A A) L f Dv := hv ▸ MultiplicativeFrames.secondFrames L Dh symmetry f F

/-- Product-exchanging symmetry proves both transverse laws for the constructed frame systems. -/
theorem transverseFrames (hv : MultiplicativeFrames.secondMultiplication L Dh symmetry = Dv)
    (hh : returnedFirst L Dv symmetry = Dh) (ht : Kernel.FramesTransverseTransport.Transverse f F Dv) :
    Biextension.Compatibility.TransverseFrames L Dh Dv f f F
      (secondFramesOfCompatible L Dh Dv symmetry f F hv) := by
  refine ⟨?_, ht⟩
  have hs := second_transverse L Dh Dv symmetry f F ht
  rw [hh] at hs
  cases hv
  exact hs

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.TransverseFrames
