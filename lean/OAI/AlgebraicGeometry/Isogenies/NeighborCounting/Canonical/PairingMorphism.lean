import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityPolarizationNaturality
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.RelativePairing

/-! # Pairing Morphism -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PairingMorphism

noncomputable section

/-! Preservation of the actual polarization map preserves its
canonical native scheme pairing on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityPolarizationNaturality.Construction OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.RelativePairing.Construction
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

variable {S : Scheme} (A B : CartierDuality.PolarizedTorsion.AbelianScheme S)
  (polA : CartierDuality.PolarizedTorsion.Polarization A) (polB : CartierDuality.PolarizedTorsion.Polarization B)
  (n : ℕ) (hn : 0 < n) (f : A.toOver ⟶ B.toOver) [IsMonHom f]

theorem canonicalPolarizationPairing_morphism
    (h : f ≫ polB.map ≫
      (AbelianScheme.FrobeniusKernel.IntrinsicCartierNaturality.Construction.nativePicardPullbackGroup A.toOver B.toOver f polA.dual polB.dual).hom.hom = polA.map)
    (T : Over S) (x y : T ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.toOver n) :
    (AbelianScheme.IsogenyQuotient.Canonical.RelativePairing.Construction.canonicalNativePolarizationPairing polB n hn).pairValue
        (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n f) (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n f) =
      (AbelianScheme.IsogenyQuotient.Canonical.RelativePairing.Construction.canonicalNativePolarizationPairing polA n hn).pairValue x y := by
  let fG := AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom A.toOver B.toOver f
  let t := AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap fG) n
  have hx := congrArg (fun a => a.hom.app (.op T) (ULift.up x))
    (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso_natural n fG)
  have hy := congrArg (fun a => a.hom.app (.op T) (ULift.up y))
    (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso_natural n fG)
  change (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk B.toOver) n).hom.hom.app (.op T)
      (ULift.up (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n f)) =
    t.hom.app (.op T) ((AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T)
      (ULift.up x)) at hx
  change (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk B.toOver) n).hom.hom.app (.op T)
      (ULift.up (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n f)) =
    t.hom.app (.op T) ((AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T)
      (ULift.up y)) at hy
  have ht := AbelianScheme.FrobeniusKernel.CartierDualityPolarizationNaturality.Construction.e56PolarizationPairing_morphism A B polA polB n hn f h T
    ((AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T) (ULift.up x))
    ((AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T) (ULift.up y))
  have he := congrArg₂ (fun a b : (B.torsionSheaf n).obj.obj (.op T) =>
    AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (B.torsionSheaf n) T
      ((polB.torsionPairing n hn).rightAdjoint.hom.app (.op T) b) a) hx hy
  apply ULift.up_injective
  exact (AbelianScheme.IsogenyQuotient.Torsion.SheafPairing.Construction.torsionSheafPairingToNative_rightValue (Grp.mk B.toOver) (Grp.mk B.toOver) n
    (polB.torsionPairing n hn) T (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n f) (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n f)).trans
    (he.trans (ht.trans (AbelianScheme.IsogenyQuotient.Torsion.SheafPairing.Construction.torsionSheafPairingToNative_rightValue
      (Grp.mk A.toOver) (Grp.mk A.toOver) n (polA.torsionPairing n hn) T x y).symm))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PairingMorphism
