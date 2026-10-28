import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCartierSheafSource
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationSheafMaps
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.WeilPairing

/-! # Intrinsic Weil Adjoints -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilAdjoints

noncomputable section

/-! Actual Weil characters intertwine the original endomorphism and
the Picard pullback that it induces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

namespace Construction

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters

variable {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.withPicardGroup.abelian) [IsMonHom ell]
    [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
    (n : ℕ) (hn : 0 < n)
    [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] [Flat ((𝟙 A : A ⟶ A) ^ n).left]
    [Surjective ((𝟙 A : A ⟶ A) ^ n).left]
    [LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left]
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))
    (p : A ⟶ A) [IsMonHom p]

theorem nativeTorsionCartierIso_endomorphism :
    (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map
        (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A p)) n).op ≫
        (CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso A D ell n hn C).hom =
      (CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso A D ell n hn C).hom ≫
        CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap
          (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicCartierNaturality.Construction.nativePicardEndomorphismGroup A p D.withPicardGroup)) n := by
  exact Intertwining.Construction.intertwining_comp _ _ _
    ((CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom.op)
    (CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf ((𝟙 A) ^ n) D.withPicardGroup C n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n))
    (Intertwining.Construction.intertwining_op_map (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S) _ _ _
      (IntrinsicMultiplicationSheafMaps.Construction.nativeMultiplicationKernelSheafIso_natural A p n))
    (IntrinsicCartierSheafSource.Construction.nativeCartierTorsionSheaf_endomorphism A p n D.withPicardGroup C)

theorem nativeWeilCharacter_endomorphism :
    CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap
        (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicCartierNaturality.Construction.nativePicardEndomorphismGroup A p D.withPicardGroup)) n ≫
        (CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso A D ell n hn C).inv =
      (CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso A D ell n hn C).inv ≫
        (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map
          (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A p)) n).op :=
  Intertwining.Construction.intertwining_inverse (CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso A D ell n hn C) _ _
    (nativeTorsionCartierIso_endomorphism A D ell n hn C p)

theorem nativeWeilPairing_endomorphism :
    CartierDuality.SheafBlocks.Construction.Schemes.ProjectorsAdjoint (CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing A D ell n hn C)
      (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A p)) n)
      (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap
        (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicCartierNaturality.Construction.nativePicardEndomorphismGroup A p D.withPicardGroup)) n) := by
  intro T x y
  rw [CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing_rightAdjoint]
  have h := congrArg (fun f => f.hom.app (.op T) y)
    (nativeWeilCharacter_endomorphism A D ell n hn C p)
  exact (CartierDuality.SheafEvaluation.Construction.Schemes.cartierDualSheafMap_value
    (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A p)) n)
    T ((CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso A D ell n hn C).inv.hom.app (.op T) y) x).symm.trans
      (congrArg (fun z => CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue
        (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n) T z x) h.symm)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilAdjoints
