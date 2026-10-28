import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Rigidity
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelFrameRigidity

/-! # Isomorphic Kernel Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicKernelFrames

noncomputable section

/-! An actual product-compatible line isomorphism identifies the unique natural transverse kernel frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationIso OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FiberIsomorphisms

variable {k : Type u} [Field k] {A B X Y : Over (Spec (.of k))}
  [GrpObj A] [GrpObj B] [GrpObj X] [GrpObj Y]
  (f : A ⟶ B) [IsMonHom f] (g : X ⟶ Y) [IsMonHom g]
  (L M : Line.Bundles.LineBundle (A ⊗ X).left) (e : L.sheaf ≅ M.sheaf)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Eh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) M) (Ev : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) M)
  (hh : FiberwiseMultiplicationIso.transportMultiplication (fst A X) (snd A X) L M e Dh = Eh)
  (hv : FiberwiseMultiplicationIso.transportMultiplication (snd A X) (fst A X) L M e Dv = Ev)

include hh hv

/-- Proper connected geometry identifies the actual first-coordinate frames through the line isomorphism. -/
theorem horizontal_frame [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    [IsAffine (Kernel.Scheme.kernelObject f).left]
    (K : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (J : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) M f Eh)
    (hK : Kernel.FramesTransverseTransport.Transverse f K Dv) (hJ : Kernel.FramesTransverseTransport.Transverse f J Ev)
    {T : Over (Spec (.of k))} (x : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ A ⊗ X)
    (ha : x ≫ Kernel.Scheme.kernelInclusion f = a ≫ fst A X) :
    Line.FiberIsomorphisms.transportFrame L M e a (K.frame x a ha) = J.frame x a ha := by
  subst Eh
  subst Ev
  exact KernelFrame.Rigidity.frame_eq f M
    (FiberwiseMultiplicationIso.transportMultiplication (fst A X) (snd A X) L M e Dh)
    (FiberwiseMultiplicationIso.transportMultiplication (snd A X) (fst A X) L M e Dv)
    (FiberwiseMultiplicationIso.transportKernelFrames (fst A X) (snd A X) L M e Dh f K) J
    (Kernel.FramesTransverseTransport.iso f M e K Dv hK) hJ x a ha

/-- The same proper-family uniqueness identifies the actual second-coordinate frames. -/
theorem vertical_frame [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [IsAffine (Kernel.Scheme.kernelObject g).left]
    (K : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv) (J : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) M g Ev)
    (hK : Kernel.FramesTransverseTransport.Transverse g K Dh) (hJ : Kernel.FramesTransverseTransport.Transverse g J Eh)
    {T : Over (Spec (.of k))} (x : T ⟶ Kernel.Scheme.kernelObject g) (a : T ⟶ A ⊗ X)
    (ha : x ≫ Kernel.Scheme.kernelInclusion g = a ≫ snd A X) :
    Line.FiberIsomorphisms.transportFrame L M e a (K.frame x a ha) = J.frame x a ha := by
  subst Eh
  subst Ev
  exact Vertical.KernelFrameRigidity.frame_eq g M
    (FiberwiseMultiplicationIso.transportMultiplication (fst A X) (snd A X) L M e Dh)
    (FiberwiseMultiplicationIso.transportMultiplication (snd A X) (fst A X) L M e Dv)
    (FiberwiseMultiplicationIso.transportKernelFrames (snd A X) (fst A X) L M e Dv g K) J
    (Kernel.FramesTransverseTransport.iso g M e K Dh hK) hJ x a ha

/-- The actual kernel-frame obstruction is preserved on every test scheme by a product-compatible line isomorphism. -/
theorem isotropic [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    [IsAffine (Kernel.Scheme.kernelObject f).left] [IsAffine (Kernel.Scheme.kernelObject g).left]
    (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
    (Jh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) M f Eh) (Jv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) M g Ev)
    (hKh : Kernel.FramesTransverseTransport.Transverse f Kh Dv) (hKv : Kernel.FramesTransverseTransport.Transverse g Kv Dh)
    (hJh : Kernel.FramesTransverseTransport.Transverse f Jh Ev) (hJv : Kernel.FramesTransverseTransport.Transverse g Jv Eh)
    (hi : Biextension.Compatibility.Isotropic L Dh Dv f g Kh Kv) :
    Biextension.Compatibility.Isotropic M Eh Ev f g Jh Jv := by
  intro T x y a hx hy
  apply (Line.FrameUnits.frameRatio_eq_one_iff _ _).mpr
  have h := (Line.FrameUnits.frameRatio_eq_one_iff _ _).mp (hi T x y a hx hy)
  exact (horizontal_frame f L M e Dh Dv Eh Ev hh hv Kh Jh hKh hJh x a hx).symm.trans
    ((congrArg (Line.FiberIsomorphisms.transportFrame L M e a) h).trans
      (vertical_frame g L M e Dh Dv Eh Ev hh hv Kv Jv hKv hJv y a hy))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicKernelFrames
