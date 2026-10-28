import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafSectionComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.RelativePairing
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues

/-! # Intrinsic Weil Value -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.IntrinsicWeilValue.Construction

noncomputable section

/-! Native torsion points retain the actual character-line Weil value
over arbitrary bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues.Construction
attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

set_option backward.isDefEq.respectTransparency false in
theorem nativeTorsionWeilImage_inclusion
    {S : Scheme} {A : CartierDuality.PolarizedTorsion.AbelianScheme S} (pol : CartierDuality.PolarizedTorsion.Polarization A)
    (n : ℕ) (T : Over S) (y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.toOver n) :
    ((y ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso A.toOver n).inv) ≫
        CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap pol.map n) ≫ TorsionQuotient.SubgroupFunctor.torsionι pol.dual.abelian n =
      (y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.toOver n) ≫ pol.map := by
  let z := y ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso A.toOver n).inv
  have hz : z ≫ TorsionQuotient.SubgroupFunctor.torsionι A.toOver n = y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.toOver n := by
    rw [Category.assoc, Intrinsic.TorsionComparison.Construction.torsionEqualizerKernelIso_inv_inclusion]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => z ≫ t) (CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap_inclusion pol.map n)).trans
      ((Category.assoc z (TorsionQuotient.SubgroupFunctor.torsionι A.toOver n) pol.map).symm.trans
        (congrArg (fun t => t ≫ pol.map) hz)))

variable {S : Scheme} {A : CartierDuality.PolarizedTorsion.AbelianScheme S} (pol : CartierDuality.PolarizedTorsion.Polarization A)
  (n : ℕ) (hn : 0 < n)
  [IsFinite ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left]
  [Flat ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left]
  [Surjective ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left]
  [LocallyOfFinitePresentation ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left]

set_option backward.isDefEq.respectTransparency false in
theorem canonicalNativePolarizationPairing_nativePointValue (T : Over S)
    (x y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.toOver n) :
    (Canonical.RelativePairing.Construction.canonicalNativePolarizationPairing pol n hn).pairValue x y =
      FrobeniusKernel.IntrinsicWeilCharacterPoints.Construction.nativeWeilPointValue A.toOver pol.representation pol.map n hn
        (FrobeniusKernel.DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation A n) T
        (x ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso A.toOver n).inv)
        ((y ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso A.toOver n).inv) ≫
          CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap pol.map n) := by
  have hx : (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T)
      (ULift.up (x ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso A.toOver n).inv)) =
      (Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T) (ULift.up x) := by
    rw [FrobeniusKernel.IntrinsicMultiplicationPointComparison.Construction.multiplicationKernelSheafIso_point]
    apply Torsion.SheafSectionComparison.Construction.torsionSheafSection_eq_of_inclusion
    rw [Category.assoc, Intrinsic.TorsionComparison.Construction.torsionEqualizerKernelIso_inv_inclusion]
  have hy : (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T)
      (ULift.up (y ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso A.toOver n).inv)) =
      (Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T) (ULift.up y) := by
    rw [FrobeniusKernel.IntrinsicMultiplicationPointComparison.Construction.multiplicationKernelSheafIso_point]
    apply Torsion.SheafSectionComparison.Construction.torsionSheafSection_eq_of_inclusion
    rw [Category.assoc, Intrinsic.TorsionComparison.Construction.torsionEqualizerKernelIso_inv_inclusion]
  have h := FrobeniusKernel.DualityIntrinsicPointValues.Construction.e56PolarizationPairing_nativePointValue A pol n hn T
    (x ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso A.toOver n).inv)
    (y ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso A.toOver n).inv)
  rw [hx, hy] at h
  exact (congrArg ULift.down (Torsion.SheafPairing.Construction.torsionSheafPairingToNative_rightValue
    (Grp.mk A.toOver) (Grp.mk A.toOver) n (pol.torsionPairing n hn) T x y)).trans h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.IntrinsicWeilValue.Construction
