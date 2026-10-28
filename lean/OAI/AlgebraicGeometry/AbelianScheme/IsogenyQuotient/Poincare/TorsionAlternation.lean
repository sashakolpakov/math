import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SymmetricKernelAlternation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.LineDescent

/-! # Torsion Alternation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionAlternation.Construction

noncomputable section

/-! Alternation of the actual full-torsion pairing used by Poincare line descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames

universe u

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

theorem compatibleSecondKernelFrame_eq
    {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle (A ⊗ A).left)
    (Dh : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst A A) (snd A A) L) (Dv : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd A A) (fst A A) L)
    (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj L.sheaf ≅ L.sheaf)
    (f : A ⟶ B) [IsMonHom f] (F : Picard.PoincareBundle.FiberwiseMultiplication.KernelFrames (fst A A) (snd A A) L f Dh)
    (hv : Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication L Dh σ = Dv)
    {T : Over S} (k : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) (c : T ⟶ A ⊗ A)
    (hc : k ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = c ≫ snd A A) :
    (Picard.PoincareBundle.Symmetric.TransverseFrames.secondFramesOfCompatible L Dh Dv σ f F hv).frame k c hc =
      (Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondFrames L Dh σ f F).frame k c hc := by
  cases hv
  rfl

theorem canonicalPoincareKernelPairing_pairing_apply
    {S : Scheme.{u}} {A B Z : Over S} [GrpObj A] [GrpObj B] [GrpObj Z]
    (φ : A ⟶ Z) [IsMonHom φ] (P : Picard.PoincareBundle.Line.Bundles.LineBundle (Z ⊗ A).left)
    (Dh : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
    (f : A ⟶ B) [IsMonHom f] (hf : Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f ≫ φ = 1)
    (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P φ).sheaf)
    (hv : Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P φ) (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) σ = Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical φ P Dv)
    (hi : Picard.PoincareBundle.Biextension.Compatibility.Interchange P Dh Dv)
    (hh : Picard.PoincareBundle.Symmetric.TransverseFrames.returnedFirst (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P φ) (Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical φ P Dv) σ =
      Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)
    (T : Over S) (x y : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) :
    Picard.PoincareBundle.Canonical.KernelPairing.pairing φ P Dh Dv f hf σ hv hi hh T x y =
      Picard.PoincareBundle.Canonical.KernelPairing.value φ P Dh Dv f hf σ hv x y := rfl

theorem canonicalPoincareKernelPairing_diagonal
    {S : Scheme.{u}} {A B Z : Over S} [GrpObj A] [GrpObj B] [GrpObj Z]
    (φ : A ⟶ Z) [IsMonHom φ] (P : Picard.PoincareBundle.Line.Bundles.LineBundle (Z ⊗ A).left)
    (Dh : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
    (f : A ⟶ B) [IsMonHom f] (hf : Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f ≫ φ = 1)
    (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P φ).sheaf)
    (hv : Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P φ) (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) σ = Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical φ P Dv)
    (hdiag : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A).left).mapIso σ =
      Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P φ)
        (DiagonalLineSymmetry.Construction.groupDiagonal A) (DiagonalLineSymmetry.Construction.groupDiagonal A) (DiagonalLineSymmetry.Construction.groupDiagonal_swap A))
    {T : Over S} (k : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) :
    Picard.PoincareBundle.Canonical.KernelPairing.value φ P Dh Dv f hf σ hv k k = 1 := by
  change Picard.PoincareBundle.Line.FrameUnits.frameRatio
    ((Picard.PoincareBundle.Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hf).frame k _ _)
    ((Picard.PoincareBundle.CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv f hf σ hv).frame k _ _) = 1
  rw [Picard.PoincareBundle.CanonicalPoincare.LineDescent.secondKernelFrames, compatibleSecondKernelFrame_eq]
  exact SymmetricKernelAlternation.Construction.symmetricKernelPairing_diagonal (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P φ) (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) σ f
    (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hf) hdiag k

set_option backward.isDefEq.respectTransparency false in
theorem poincareNativeTorsionPairing_alternating
    {S : Scheme.{u}} {A Z : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj Z] [IsCommMonObj Z]
    (φ : A ⟶ Z) [IsMonHom φ] (P : Picard.PoincareBundle.Line.Bundles.LineBundle (Z ⊗ A).left)
    (Dh : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
    (n : ℕ)
    (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf)
    (hv : Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)) (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) σ = Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv)
    (hi : Picard.PoincareBundle.Biextension.Compatibility.Interchange P Dh Dv)
    (hh : Picard.PoincareBundle.Symmetric.TransverseFrames.returnedFirst (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)) (Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) σ =
      Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh)
    (hdiag : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A).left).mapIso σ =
      Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n))
        (DiagonalLineSymmetry.Construction.groupDiagonal A) (DiagonalLineSymmetry.Construction.groupDiagonal A) (DiagonalLineSymmetry.Construction.groupDiagonal_swap A))
    (T : Over S) (x : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A n) :
    (LineDescent.Construction.poincareNativeTorsionPairing φ P Dh Dv n σ hv hi hh).pairValue x x = 1 := by
  apply CartierDuality.UnitValueDetection.Construction.Schemes.multiplicativeGroupUnitHom_injective T
  rw [LineDescent.Construction.poincareNativeTorsionPairing_value, map_one]
  rw [Picard.PoincareBundle.TorsionPairing.Poincare.torsionPairing, canonicalPoincareKernelPairing_pairing_apply]
  exact canonicalPoincareKernelPairing_diagonal (φ ^ n) P Dh Dv ((𝟙 A) ^ n)
    (Picard.PoincareBundle.TorsionPairing.Poincare.torsion_annihilation φ n) σ hv hdiag x

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionAlternation.Construction
