import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionAlternation

/-! # Kernel Frame Ratio -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.KernelFrameRatio.Construction

noncomputable section

/-! The canonical PoincareBundle kernel value is the ratio of its first frame
and the actual symmetry-transported second frame at the chosen point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits

universe u

set_option backward.isDefEq.respectTransparency false in
theorem canonicalKernelPairing_frameRatio_at {S : Scheme.{u}} {A B Z T : Over S}
    [GrpObj A] [GrpObj B] [GrpObj Z] (φ : A ⟶ Z) [IsMonHom φ]
    (P : Picard.PoincareBundle.Line.Bundles.LineBundle (Z ⊗ A).left)
    (Dh : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
    (f : A ⟶ B) [IsMonHom f] (hf : Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f ≫ φ = 1)
    (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P φ).sheaf)
    (hv : Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P φ) (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) σ = Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical φ P Dv)
    (k l : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) (a : T ⟶ A ⊗ A)
    (hk : k ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = a ≫ fst A A) (hl : l ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = a ≫ snd A A) :
    Picard.PoincareBundle.Canonical.KernelPairing.value φ P Dh Dv f hf σ hv k l =
      Picard.PoincareBundle.Line.FrameUnits.frameRatio ((Picard.PoincareBundle.Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hf).frame k a hk)
        ((Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondFrames (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P φ) (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) σ f (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hf)).frame l a hl) := by
  have h := Picard.PoincareBundle.Canonical.KernelPairing.value_at φ P Dh Dv f hf σ hv k l a hk hl
  change Picard.PoincareBundle.Canonical.KernelPairing.value φ P Dh Dv f hf σ hv k l =
    Picard.PoincareBundle.Line.FrameUnits.frameRatio ((Picard.PoincareBundle.Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hf).frame k a hk)
      ((Picard.PoincareBundle.CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv f hf σ hv).frame l a hl) at h
  rw [Picard.PoincareBundle.CanonicalPoincare.LineDescent.secondKernelFrames, Poincare.TorsionAlternation.Construction.compatibleSecondKernelFrame_eq] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.KernelFrameRatio.Construction
