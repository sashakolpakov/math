import OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondKernelFrameEvaluation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.IntersectionObstructionValues
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

/-! # Global Kernel Isotropy -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.GlobalKernelIsotropy

noncomputable section

/-! Canonical scheme-valued kernel isotropy gives exactly the global-frame obstruction used by inducing-line descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (Q : Line.Bundles.LineBundle (A ⊗ A).left)
  (D : FiberwiseMultiplication.Multiplication (fst A A) (snd A A) Q) (K : FiberwiseMultiplication.KernelFrames (fst A A) (snd A A) Q f D)
  (Dv : FiberwiseMultiplication.Multiplication (snd A A) (fst A A) Q)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj Q.sheaf ≅ Q.sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication Q D σ = Dv)

/-- The canonical pointwise kernel obstruction equals the ratio of the constructed global frames. -/
theorem obstruction_eq {T : Over S} (a b : T ⟶ Kernel.Scheme.kernelObject f) :
    Kernel.IntersectionFrames.obstruction (Kernel.Scheme.kernelInclusion f) (Kernel.Scheme.kernelInclusion f) Q
        (KernelFrame.Global.globalFrame f Q D K)
        (Symmetric.KernelTrivialization.secondFrame (Kernel.Scheme.kernelInclusion f) Q (KernelFrame.Global.globalFrame f Q D K) σ) a b =
      Biextension.Compatibility.kernelObstruction Q D Dv f f K
        (Symmetric.TransverseFrames.secondFramesOfCompatible Q D Dv σ f K hv) a b
        (lift (a ≫ Kernel.Scheme.kernelInclusion f) (b ≫ Kernel.Scheme.kernelInclusion f)) (lift_fst _ _).symm (lift_snd _ _).symm := by
  have hh := UniversalKernelFrameEvaluation.atPoint f Q D K (lift a (b ≫ Kernel.Scheme.kernelInclusion f)) a
    (lift (a ≫ Kernel.Scheme.kernelInclusion f) (b ≫ Kernel.Scheme.kernelInclusion f)) (lift_fst _ _) (lift_fst _ _).symm
    (IntersectionFrameValues.horizontal_pair (Kernel.Scheme.kernelInclusion f) (Kernel.Scheme.kernelInclusion f) a b)
  have hs := SecondKernelFrameEvaluation.Universal.pair_value f Q D K Dv σ hv a b
  exact (IntersectionObstructionValues.value_eq (Kernel.Scheme.kernelInclusion f) (Kernel.Scheme.kernelInclusion f) Q
    (KernelFrame.Global.globalFrame f Q D K)
    (Symmetric.KernelTrivialization.secondFrame (Kernel.Scheme.kernelInclusion f) Q (KernelFrame.Global.globalFrame f Q D K) σ) a b).trans
    (congrArg₂ Line.FrameUnits.frameRatio hh hs)

/-- The existing scheme-valued canonical isotropy hypothesis supplies global-frame isotropy with no extra assumption. -/
theorem isotropic (hi : Biextension.Compatibility.Isotropic Q D Dv f f K
    (Symmetric.TransverseFrames.secondFramesOfCompatible Q D Dv σ f K hv)) :
    ∀ (T : Over S) (a b : T ⟶ Kernel.Scheme.kernelObject f),
      Kernel.IntersectionFrames.obstruction (Kernel.Scheme.kernelInclusion f) (Kernel.Scheme.kernelInclusion f) Q
        (KernelFrame.Global.globalFrame f Q D K)
        (Symmetric.KernelTrivialization.secondFrame (Kernel.Scheme.kernelInclusion f) Q (KernelFrame.Global.globalFrame f Q D K) σ) a b = 1 := by
  intro T a b
  exact (obstruction_eq f Q D K Dv σ hv a b).trans
    (hi T a b (lift (a ≫ Kernel.Scheme.kernelInclusion f) (b ≫ Kernel.Scheme.kernelInclusion f)) (lift_fst _ _).symm (lift_snd _ _).symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.GlobalKernelIsotropy
