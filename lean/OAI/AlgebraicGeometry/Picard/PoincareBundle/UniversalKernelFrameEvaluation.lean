import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Global
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

/-! # Universal Kernel Frame Evaluation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.UniversalKernelFrameEvaluation

noncomputable section

/-! Evaluation of the universal actual kernel frame recovers the original natural frame system. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {S : Scheme.{u}} {A B X : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (Q : Line.Bundles.LineBundle (A ⊗ X).left)
  (D : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) Q)
  (K : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) Q f D)

/-- The original frame at any subgroup-valued point is the actual evaluation of the constructed global frame. -/
theorem atPoint {T : Over S} (q : T ⟶ Kernel.Scheme.kernelObject f ⊗ X) (k : T ⟶ Kernel.Scheme.kernelObject f) (x : T ⟶ A ⊗ X)
    (hqk : q ≫ fst (Kernel.Scheme.kernelObject f) X = k) (hk : k ≫ Kernel.Scheme.kernelInclusion f = x ≫ fst A X)
    (hqx : q ≫ (Kernel.Scheme.kernelInclusion f ⊗ₘ 𝟙 X) = x) :
    GlobalPullbackFrame.atPoint (Kernel.Scheme.kernelInclusion f ⊗ₘ 𝟙 X) Q (KernelFrame.Global.globalFrame f Q D K)
        q x hqx = K.frame k x hk := by
  have hn := K.natural q (fst (Kernel.Scheme.kernelObject f) X) k hqk (Kernel.Scheme.kernelInclusion f ⊗ₘ 𝟙 X) x
    (KernelFrame.Global.universalPoint_fst f) hk hqx
  have hc := GlobalPullbackFrame.comparison_eq (Kernel.Scheme.kernelInclusion f ⊗ₘ 𝟙 X) Q q x hqx
  apply Iso.ext
  exact (congrArg (fun c => (FrameRatioPullback.pullFrame q.left (KernelFrame.Global.globalFrame f Q D K) ≪≫ c).hom) hc).trans hn

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.UniversalKernelFrameEvaluation
