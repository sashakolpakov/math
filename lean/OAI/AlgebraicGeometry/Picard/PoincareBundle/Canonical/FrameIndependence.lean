import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Comparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent

/-! # Frame Independence -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.FrameIndependence

noncomputable section

/-!
# The canonical Poincare frames depend only on the included ambient point

This permits comparison of the quotient-kernel pairing with the same construction on the full
torsion subgroup scheme. All points remain arbitrary scheme-valued points.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent
open OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Comparison

variable {S : Scheme.{u}} {A B C Z : Over S} [GrpObj A] [GrpObj B] [GrpObj C] [GrpObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P)
  (f : A ⟶ B) (g : A ⟶ C) [IsMonHom f] [IsMonHom g]
  (hf : Kernel.Scheme.kernelInclusion f ≫ φ = 1) (hg : Kernel.Scheme.kernelInclusion g ≫ φ = 1)

/-- The first canonical frame depends on the actual line fiber and its neutral image, not a kernel presentation. -/
theorem first_frame_eq {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g)
    (a : T ⟶ A ⊗ A) (hk : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ fst A A)
    (hl : l ≫ Kernel.Scheme.kernelInclusion g = a ≫ fst A A) :
    (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hf).frame k a hk = (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh g hg).frame l a hl := rfl

variable (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) e = Poincare.TransverseFrames.sourceVertical φ P Dv)

/-- Actual symmetry gives the same second canonical frame for two presentations of the included point. -/
theorem second_frame_eq {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g)
    (a : T ⟶ A ⊗ A) (hk : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ snd A A)
    (hl : l ≫ Kernel.Scheme.kernelInclusion g = a ≫ snd A A) :
    (CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv f hf e hv).frame k a hk =
      (CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv g hg e hv).frame l a hl := by
  unfold CanonicalPoincare.LineDescent.secondKernelFrames
  rw [KernelFrame.Comparison.compatible_second_frame, KernelFrame.Comparison.compatible_second_frame, KernelFrame.Comparison.second_frame, KernelFrame.Comparison.second_frame]
  rfl

/-- The actual unit-valued obstruction is independent of the kernel presentation of its two ambient coordinates. -/
theorem obstruction_eq {T : Over S}
    (k l : T ⟶ Kernel.Scheme.kernelObject f) (k' l' : T ⟶ Kernel.Scheme.kernelObject g) (a : T ⟶ A ⊗ A)
    (hk : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ fst A A) (hl : l ≫ Kernel.Scheme.kernelInclusion f = a ≫ snd A A)
    (hk' : k' ≫ Kernel.Scheme.kernelInclusion g = a ≫ fst A A) (hl' : l' ≫ Kernel.Scheme.kernelInclusion g = a ≫ snd A A) :
    Biextension.Compatibility.kernelObstruction (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)
      (Poincare.TransverseFrames.sourceVertical φ P Dv) f f (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hf) (CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv f hf e hv)
      k l a hk hl =
    Biextension.Compatibility.kernelObstruction (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)
      (Poincare.TransverseFrames.sourceVertical φ P Dv) g g (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh g hg) (CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv g hg e hv)
      k' l' a hk' hl' :=
  congrArg₂ Line.FrameUnits.frameRatio (first_frame_eq φ P Dh f g hf hg k k' a hk hk')
    (second_frame_eq φ P Dh f g hf hg Dv e hv l l' a hl hl')

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.FrameIndependence
