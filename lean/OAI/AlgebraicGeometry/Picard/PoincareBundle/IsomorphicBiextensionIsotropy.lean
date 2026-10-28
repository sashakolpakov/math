import OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicKernelFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.OriginNormalization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseKernelOriginUnits

/-! # Isomorphic Biextension Isotropy -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicBiextensionIsotropy

noncomputable section

/-! Isomorphism of the actual underlying line families preserves their canonical transverse-frame isotropy. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

variable {k : Type u} [Field k] {A B X Y : Over (Spec (.of k))}
  [GrpObj A] [GrpObj B] [GrpObj X] [GrpObj Y] [IsCommMonObj A] [IsCommMonObj X]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  (f : A ⟶ B) [IsMonHom f] (g : X ⟶ Y) [IsMonHom g]
  [IsAffine (Kernel.Scheme.kernelObject f).left] [IsAffine (Kernel.Scheme.kernelObject g).left]
  (L M : Line.Bundles.LineBundle (A ⊗ X).left) (e : L.sheaf ≅ M.sheaf)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Eh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) M) (Ev : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) M)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (Jh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) M f Eh) (Jv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) M g Ev)
  (hKh : Kernel.FramesTransverseTransport.Transverse f Kh Dv) (hKv : Kernel.FramesTransverseTransport.Transverse g Kv Dh)
  (hJh : Kernel.FramesTransverseTransport.Transverse f Jh Ev) (hJv : Kernel.FramesTransverseTransport.Transverse g Jv Eh)

include e hKh hKv hJh hJv

/-- Actual line-family isomorphism suffices: origin normalization proves compatibility with the two products. -/
theorem isotropic (hi : Biextension.Compatibility.Isotropic L Dh Dv f g Kh Kv) : Biextension.Compatibility.Isotropic M Eh Ev f g Jh Jv := by
  obtain ⟨e', hh, hv⟩ := Biextension.OriginNormalization.exists_productCompatible_iso A X L M Dh Dv Eh Ev e
    (TransverseKernelOriginUnits.unitFrames_eq f L Dh Dv Kh hKh 1
      (MonObj.one_comp (fst A X)) (MonObj.one_comp (snd A X)))
    (TransverseKernelOriginUnits.unitFrames_eq f M Eh Ev Jh hJh 1
      (MonObj.one_comp (fst A X)) (MonObj.one_comp (snd A X)))
  exact IsomorphicKernelFrames.isotropic f g L M e' Dh Dv Eh Ev hh hv Kh Kv Jh Jv hKh hKv hJh hJv hi

/-- Triviality of the actual kernel-frame pairing depends only on the underlying isomorphic line families. -/
theorem isotropic_iff : Biextension.Compatibility.Isotropic L Dh Dv f g Kh Kv ↔ Biextension.Compatibility.Isotropic M Eh Ev f g Jh Jv :=
  ⟨isotropic f g L M e Dh Dv Eh Ev Kh Kv Jh Jv hKh hKv hJh hJv,
    isotropic f g M L e.symm Eh Ev Dh Dv Jh Jv Kh Kv hJh hJv hKh hKv⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicBiextensionIsotropy
