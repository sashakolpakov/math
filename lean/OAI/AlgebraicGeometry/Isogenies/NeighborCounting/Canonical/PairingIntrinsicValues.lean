import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.RelativePairing
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationKernelSheafComparison

/-! # Pairing Intrinsic Values -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PairingIntrinsicValues.Intrinsic

noncomputable section

/-! The original canonical scheme pairing has the exact native
character-line value on the original multiplication-kernel points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues.Construction
attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative
attribute [local instance] AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues.Construction.e56PointPolarization_preserves

variable {S : Scheme} (A : CartierDuality.PolarizedTorsion.AbelianScheme S) (pol : CartierDuality.PolarizedTorsion.Polarization A)
  (n : ℕ) (hn : 0 < n)
  [IsFinite ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left]
  [Flat ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left]
  [Surjective ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left]
  [LocallyOfFinitePresentation ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left]

theorem canonicalPolarizationPairing_nativePointValue (T : Over S)
    (x y : T ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.toOver n) :
    (AbelianScheme.IsogenyQuotient.Canonical.RelativePairing.Construction.canonicalNativePolarizationPairing pol n hn).pairValue x y =
      AbelianScheme.FrobeniusKernel.IntrinsicWeilCharacterPoints.Construction.nativeWeilPointValue A.toOver pol.representation pol.map n hn
        (AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation A n) T
        (x ≫ (AbelianScheme.IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.toOver) n).inv.hom.hom)
        ((y ≫ (AbelianScheme.IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.toOver) n).inv.hom.hom) ≫
          AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap pol.map n) := by
  have hv := AbelianScheme.IsogenyQuotient.Torsion.SheafPairing.Construction.torsionSheafPairingToNative_rightValue (Grp.mk A.toOver) (Grp.mk A.toOver) n
    (pol.torsionPairing n hn) T x y
  have hx := AbelianScheme.IsogenyQuotient.MultiplicationKernelSheafComparison.Construction.multiplicationKernelSheafIso_native_value (Grp.mk A.toOver) n T x
  have hy := AbelianScheme.IsogenyQuotient.MultiplicationKernelSheafComparison.Construction.multiplicationKernelSheafIso_native_value (Grp.mk A.toOver) n T y
  have he := congrArg₂ (fun a b : (A.torsionSheaf n).obj.obj (.op T) =>
    AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (A.torsionSheaf n) T
      ((pol.torsionPairing n hn).rightAdjoint.hom.app (.op T) b) a) hx.symm hy.symm
  exact (congrArg ULift.down hv).trans ((congrArg ULift.down he).trans
    (AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues.Construction.e56PolarizationPairing_nativePointValue A pol n hn T
      (x ≫ (AbelianScheme.IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.toOver) n).inv.hom.hom)
      (y ≫ (AbelianScheme.IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.toOver) n).inv.hom.hom)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PairingIntrinsicValues.Intrinsic
