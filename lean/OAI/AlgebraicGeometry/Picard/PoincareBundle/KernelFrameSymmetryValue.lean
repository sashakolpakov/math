import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Comparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.SymmetryFibers

/-! # Kernel Frame Symmetry Value -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrameSymmetryValue.Second

noncomputable section

/-! The canonical second kernel-frame system evaluates by the actual symmetry on the first frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (Q : Line.Bundles.LineBundle (A ⊗ A).left)
  (D : FiberwiseMultiplication.Multiplication (fst A A) (snd A A) Q) (K : FiberwiseMultiplication.KernelFrames (fst A A) (snd A A) Q f D)
  (Dv : FiberwiseMultiplication.Multiplication (snd A A) (fst A A) Q)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj Q.sheaf ≅ Q.sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication Q D σ = Dv)

/-- The compatible second frame is the first frame at the exchanged point followed by the
actual fiber symmetry; product identification changes no frame. -/
theorem frame_value {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (x : T ⟶ A ⊗ A)
    (hk : k ≫ Kernel.Scheme.kernelInclusion f = x ≫ snd A A) :
    (Symmetric.TransverseFrames.secondFramesOfCompatible Q D Dv σ f K hv).frame k x hk =
      K.frame k (x ≫ (β_ A A).hom) (KernelFrame.Comparison.exchanged_kernel f k x hk) ≪≫
        Line.SymmetryFibers.atPoint Q (β_ A A).hom σ x := by
  have hc := KernelFrame.Comparison.compatible_second_frame f Q D K Dv σ hv k x hk
  have hs := KernelFrame.Comparison.second_frame f Q D K σ k x hk
  exact (hc.trans hs).trans (Iso.trans_assoc _ _ _)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrameSymmetryValue.Second
