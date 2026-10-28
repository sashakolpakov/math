import OAI.AlgebraicGeometry.Picard.PoincareBundle.ExchangedKernelFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicBiextensionIsotropy

/-! # Kernel Isotropy -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.KernelIsotropy

noncomputable section

/-! Actual symmetry of the line family exchanges the two kernel-isotropy conditions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility OAI.AlgebraicGeometry.Picard.PoincareBundle.ExchangedKernelFrames

variable {k : Type u} [Field k] {A B C : Over (Spec (.of k))}
  [GrpObj A] [GrpObj B] [GrpObj C] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (f : A ⟶ B) [IsMonHom f] (g : A ⟶ C) [IsMonHom g]
  [IsAffine (Kernel.Scheme.kernelObject f).left] [IsAffine (Kernel.Scheme.kernelObject g).left]
  (L : Line.Bundles.LineBundle (A ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A A) (snd A A) L) (Dv : FiberwiseMultiplication.Multiplication (snd A A) (fst A A) L)
  (σ : (L.pullback (β_ A A).hom.left).sheaf ≅ L.sheaf)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A A) (snd A A) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A A) (fst A A) L f Dv)
  (Jh : FiberwiseMultiplication.KernelFrames (fst A A) (snd A A) L g Dh) (Jv : FiberwiseMultiplication.KernelFrames (snd A A) (fst A A) L g Dv)
  (hKh : Kernel.FramesTransverseTransport.Transverse f Kh Dv) (hKv : Kernel.FramesTransverseTransport.Transverse f Kv Dh)
  (hJh : Kernel.FramesTransverseTransport.Transverse g Jh Dv) (hJv : Kernel.FramesTransverseTransport.Transverse g Jv Dh)

include σ hKh hKv hJh hJv

/-- Symmetry of the actual line, followed by proved origin normalization, reverses kernel orthogonality. -/
theorem flip (hi : Biextension.Compatibility.Isotropic L Dh Dv f g Kh Jv) : Biextension.Compatibility.Isotropic L Dh Dv g f Jh Kv :=
  IsomorphicBiextensionIsotropy.isotropic g f (L.pullback (β_ A A).hom.left) L σ
    (ExchangedKernelFrames.horizontal L Dv) (ExchangedKernelFrames.vertical L Dh) Dh Dv
    (ExchangedKernelFrames.firstFrames g L Dv Jv) (ExchangedKernelFrames.secondFrames f L Dh Kh) Jh Kv
    (ExchangedKernelFrames.first_transverse g L Dh Dv Jv hJv) (ExchangedKernelFrames.second_transverse f L Dh Dv Kh hKh) hJh hKv
    (ExchangedKernelFrames.isotropic f g L Dh Dv Kh Jv hi)

/-- Full scheme-valued kernel orthogonality is independent of the argument order for the symmetric family. -/
theorem iff_flip : Biextension.Compatibility.Isotropic L Dh Dv f g Kh Jv ↔ Biextension.Compatibility.Isotropic L Dh Dv g f Jh Kv :=
  ⟨flip f g L Dh Dv σ Kh Kv Jh Jv hKh hKv hJh hJv,
    flip g f L Dh Dv σ Jh Jv Kh Kv hJh hJv hKh hKv⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.KernelIsotropy
