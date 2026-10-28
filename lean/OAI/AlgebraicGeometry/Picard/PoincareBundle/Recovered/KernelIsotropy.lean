import OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrameIsotropy
import OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicBiextensionIsotropy

/-! # Kernel Isotropy -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.KernelIsotropy

noncomputable section

/-! Actual recovery of a quotient line family proves kernel orthogonality in the source family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrameIsotropy

variable {k : Type u} [Field k] {A B C : Over (Spec (.of k))}
  [GrpObj A] [GrpObj B] [GrpObj C] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (f : A ⟶ B) [IsMonHom f] (m : B ⟶ C) [IsMonHom m]
  [IsAffine (Kernel.Scheme.kernelObject (f ≫ m)).left] [IsAffine (Kernel.Scheme.kernelObject (f ≫ 𝟙 B)).left]
  (L : Line.Bundles.LineBundle (B ⊗ B).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst B B) (snd B B) L) (Dv : FiberwiseMultiplication.Multiplication (snd B B) (fst B B) L)
  (K : FiberwiseMultiplication.KernelFrames (fst B B) (snd B B) L m Dh) (hK : Kernel.FramesTransverseTransport.Transverse m K Dv)
  (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (M : Line.Bundles.LineBundle (A ⊗ A).left)
  (Eh : FiberwiseMultiplication.Multiplication (fst A A) (snd A A) M) (Ev : FiberwiseMultiplication.Multiplication (snd A A) (fst A A) M)
  (Jh : FiberwiseMultiplication.KernelFrames (fst A A) (snd A A) M (f ≫ m) Eh)
  (Jv : FiberwiseMultiplication.KernelFrames (snd A A) (fst A A) M (f ≫ 𝟙 B) Ev)
  (hJh : Kernel.FramesTransverseTransport.Transverse (f ≫ m) Jh Ev) (hJv : Kernel.FramesTransverseTransport.Transverse (f ≫ 𝟙 B) Jv Eh)
  (e : (L.pullback (f ⊗ₘ f).left).sheaf ≅ M.sheaf)

include hK hi hJh hJv e

/-- The recovered source family has trivial actual pairing on the inverse-image kernel against the quotient kernel. -/
theorem isotropic : Biextension.Compatibility.Isotropic M Eh Ev (f ≫ m) (f ≫ 𝟙 B) Jh Jv :=
  IsomorphicBiextensionIsotropy.isotropic (f ≫ m) (f ≫ 𝟙 B) (L.pullback (f ⊗ₘ f).left) M e
    (Pulled.KernelFrameIsotropy.horizontalMultiplication f f L Dh) (Pulled.KernelFrameIsotropy.verticalMultiplication f f L Dv) Eh Ev
    (Pulled.KernelFrameIsotropy.horizontal f f L Dh m K) (Pulled.KernelFrameIsotropy.vertical f f L Dv) Jh Jv
    (Pulled.KernelFrameIsotropy.horizontal_transverse f f L Dh Dv m K hK) (Pulled.KernelFrameIsotropy.vertical_transverse f f L Dh Dv hi) hJh hJv
    (Pulled.KernelFrameIsotropy.isotropic f f L Dh Dv m K hK)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.KernelIsotropy
