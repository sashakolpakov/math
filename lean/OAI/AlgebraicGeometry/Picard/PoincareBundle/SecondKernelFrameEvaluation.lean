import OAI.AlgebraicGeometry.Picard.PoincareBundle.UniversalKernelFrameEvaluation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrameSymmetryValue
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.FramePointSymmetry

/-! # Second Kernel Frame Evaluation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondKernelFrameEvaluation.Universal

noncomputable section

/-! The global symmetry-constructed second frame recovers the canonical second kernel-frame system. -/

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

/-- The second global frame and the canonical second frame agree on every kernel pair. -/
theorem pair_value {T : Over S} (a b : T ⟶ Kernel.Scheme.kernelObject f) :
    GlobalPullbackFrame.atPoint (𝟙 A ⊗ₘ Kernel.Scheme.kernelInclusion f) Q
        (Symmetric.KernelTrivialization.secondFrame (Kernel.Scheme.kernelInclusion f) Q (KernelFrame.Global.globalFrame f Q D K) σ)
        (lift (a ≫ Kernel.Scheme.kernelInclusion f) b) (lift (a ≫ Kernel.Scheme.kernelInclusion f) (b ≫ Kernel.Scheme.kernelInclusion f))
        (IntersectionFrameValues.vertical_pair (Kernel.Scheme.kernelInclusion f) (Kernel.Scheme.kernelInclusion f) a b) =
      (Symmetric.TransverseFrames.secondFramesOfCompatible Q D Dv σ f K hv).frame b
        (lift (a ≫ Kernel.Scheme.kernelInclusion f) (b ≫ Kernel.Scheme.kernelInclusion f)) (lift_snd _ _).symm := by
  let s := KernelFrame.Global.globalFrame f Q D K
  let x := lift (a ≫ Kernel.Scheme.kernelInclusion f) (b ≫ Kernel.Scheme.kernelInclusion f)
  have ht := Kernel.IntersectionSymmetry.secondFrame_eq (Kernel.Scheme.kernelInclusion f) Q s σ
  have ht' := congrArg (fun t => GlobalPullbackFrame.atPoint (𝟙 A ⊗ₘ Kernel.Scheme.kernelInclusion f) Q t
    (lift (a ≫ Kernel.Scheme.kernelInclusion f) b) x (IntersectionFrameValues.vertical_pair (Kernel.Scheme.kernelInclusion f) (Kernel.Scheme.kernelInclusion f) a b)) ht
  have he := SymmetryTransportedFrames.evaluation (Kernel.Scheme.kernelInclusion f ⊗ₘ 𝟙 A) Q s (β_ A A).hom σ
    (β_ A (Kernel.Scheme.kernelObject f)).hom (𝟙 A ⊗ₘ Kernel.Scheme.kernelInclusion f) (Symmetric.KernelTrivialization.exchange_square (Kernel.Scheme.kernelInclusion f)).symm
    (lift (a ≫ Kernel.Scheme.kernelInclusion f) b) (lift b (a ≫ Kernel.Scheme.kernelInclusion f)) x
    (IntersectionFrameValues.vertical_pair (Kernel.Scheme.kernelInclusion f) (Kernel.Scheme.kernelInclusion f) a b)
    (lift_braiding_hom _ _) (Isotropic.FramePointSymmetry.exchanged_pair (Kernel.Scheme.kernelInclusion f) a b)
  have hp := UniversalKernelFrameEvaluation.atPoint f Q D K (lift b (a ≫ Kernel.Scheme.kernelInclusion f)) b
    (x ≫ (β_ A A).hom) (lift_fst _ _) (KernelFrame.Comparison.exchanged_kernel f b x (lift_snd _ _).symm)
    (Isotropic.FramePointSymmetry.exchanged_pair (Kernel.Scheme.kernelInclusion f) a b)
  have hc := KernelFrameSymmetryValue.Second.frame_value f Q D K Dv σ hv b x (lift_snd _ _).symm
  exact ht'.trans (he.trans ((congrArg (fun t => t ≪≫ Line.SymmetryFibers.atPoint Q (β_ A A).hom σ x) hp).trans hc.symm))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondKernelFrameEvaluation.Universal
