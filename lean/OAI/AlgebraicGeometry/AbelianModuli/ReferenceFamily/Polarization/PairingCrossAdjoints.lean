import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityWeilNaturality
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityPolarizationAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.IntrinsicAdjoints

/-! # Pairing Cross Adjoints -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PairingCrossAdjoints

noncomputable section

/-! A polarization square between two abelian schemes gives the
cross-adjoint identity for their actual canonical torsion pairings.
The native comparison retains every test-scheme value. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.IntrinsicAdjoints.Construction

attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

theorem e56PolarizationPairing_cross_adjoint
    {S : Scheme.{0}} (A B : CartierDuality.PolarizedTorsion.AbelianScheme S)
    (pA : CartierDuality.PolarizedTorsion.Polarization A) (pB : CartierDuality.PolarizedTorsion.Polarization B)
    (n : ℕ) (hn : 0 < n) (q : A.toOver ⟶ B.toOver) [IsMonHom q]
    (v : B.toOver ⟶ A.toOver) [IsMonHom v]
    (h : v ≫ pA.map = pB.map ≫
      (AbelianScheme.FrobeniusKernel.IntrinsicCartierNaturality.Construction.nativePicardPullbackGroup A.toOver B.toOver q pA.dual pB.dual).hom.hom)
    (T : Over S) (x : (A.torsionSheaf n).obj.obj (.op T))
    (y : (B.torsionSheaf n).obj.obj (.op T)) :
    AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (B.torsionSheaf n) T
      ((pB.torsionPairing n hn).rightAdjoint.hom.app (.op T) y)
      ((AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom A.toOver B.toOver q)) n).hom.app (.op T) x) =
    AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (A.torsionSheaf n) T
      ((pA.torsionPairing n hn).rightAdjoint.hom.app (.op T)
        ((AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom B.toOver A.toOver v)) n).hom.app (.op T) y)) x := by
  let r := AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom B.toOver A.toOver v
  let d := AbelianScheme.FrobeniusKernel.IntrinsicCartierNaturality.Construction.nativePicardPullbackGroup A.toOver B.toOver q pA.dual pB.dual
  let a := AbelianScheme.FrobeniusKernel.CartierDualityPolarizationAdjoints.Construction.e56PolarizationGroupHom A pA
  let b := AbelianScheme.FrobeniusKernel.CartierDualityPolarizationAdjoints.Construction.e56PolarizationGroupHom B pB
  have hs : r ≫ a = b ≫ d := by
    apply Grp.hom_ext
    exact h
  have hr : AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap r ≫ AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a =
      AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap b ≫ AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap d :=
    (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp r a).symm.trans
      ((congrArg AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap hs).trans (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp b d))
  have ht := AbelianScheme.FrobeniusKernel.IntrinsicTorsionSheafFunctor.Construction.torsionSheafMap_square (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap r) (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap d)
    (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap b) (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a) hr n
  have hy := congrArg (fun f => f.hom.app (.op T) y) ht
  change (pA.torsionMap n).hom.app (.op T)
      ((AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap r) n).hom.app (.op T) y) =
    (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap d) n).hom.app (.op T)
      ((pB.torsionMap n).hom.app (.op T) y) at hy
  rw [CartierDuality.PolarizedTorsion.Polarization.torsionPairing, AbelianScheme.FrobeniusKernel.SheafPairingAdjoints.Construction.pairing_restrict_rightAdjoint,
    CartierDuality.PolarizedTorsion.Polarization.torsionPairing, AbelianScheme.FrobeniusKernel.SheafPairingAdjoints.Construction.pairing_restrict_rightAdjoint]
  change AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (B.torsionSheaf n) T
      ((pB.weilPairing n hn).rightAdjoint.hom.app (.op T)
        ((pB.torsionMap n).hom.app (.op T) y)) _ =
    AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (A.torsionSheaf n) T
      ((pA.weilPairing n hn).rightAdjoint.hom.app (.op T)
        ((pA.torsionMap n).hom.app (.op T)
          ((AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap r) n).hom.app (.op T) y))) x
  rw [hy]
  exact AbelianScheme.FrobeniusKernel.CartierDualityWeilNaturality.Construction.e56WeilPairing_morphism A B pA pB n hn q T x ((pB.torsionMap n).hom.app (.op T) y)

theorem torsionSheafPairingToNative_cross_adjoint
    {S : Scheme.{0}} (G H : Grp (Over S)) [IsCommMonObj G.X] [IsCommMonObj H.X]
    (n : ℕ)
    (eG : AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n)
      (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n))
    (eH : AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H) n)
      (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H) n))
    (q : G ⟶ H) (v : H ⟶ G)
    (h : ∀ (T : Over S)
      (x : (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n).obj.obj (.op T))
      (y : (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H) n).obj.obj (.op T)),
      AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H) n) T
        (eH.rightAdjoint.hom.app (.op T) y)
        ((AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap q) n).hom.app (.op T) x) =
      AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n) T
        (eG.rightAdjoint.hom.app (.op T)
          ((AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap v) n).hom.app (.op T) y)) x)
    (T : Over S) (x : T ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme G.X n) (y : T ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme H.X n) :
    (AbelianScheme.IsogenyQuotient.Torsion.SheafPairing.Construction.torsionSheafPairingToNative H H n eH).pairValue (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q.hom.hom) y =
      (AbelianScheme.IsogenyQuotient.Torsion.SheafPairing.Construction.torsionSheafPairingToNative G G n eG).pairValue x (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n v.hom.hom) := by
  have hx := congrArg (fun f => f.hom.app (.op T) (ULift.up x)) (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso_natural n q)
  have hy := congrArg (fun f => f.hom.app (.op T) (ULift.up y)) (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso_natural n v)
  change (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso H n).hom.hom.app (.op T) (ULift.up (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q.hom.hom)) =
    (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap q) n).hom.app (.op T)
      ((AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso G n).hom.hom.app (.op T) (ULift.up x)) at hx
  change (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso G n).hom.hom.app (.op T) (ULift.up (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n v.hom.hom)) =
    (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap v) n).hom.app (.op T)
      ((AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionSheafIso H n).hom.hom.app (.op T) (ULift.up y)) at hy
  apply ULift.up_injective
  rw [AbelianScheme.IsogenyQuotient.Torsion.SheafPairing.Construction.torsionSheafPairingToNative_rightValue, AbelianScheme.IsogenyQuotient.Torsion.SheafPairing.Construction.torsionSheafPairingToNative_rightValue, hx, hy]
  exact h T _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PairingCrossAdjoints
