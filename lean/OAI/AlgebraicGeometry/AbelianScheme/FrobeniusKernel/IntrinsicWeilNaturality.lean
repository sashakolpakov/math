import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCartierSheafNaturality
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationNaturality
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.WeilPairing

/-! # Intrinsic Weil Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilNaturality

noncomputable section

/-! The actual Weil pairing is adjoint to a source morphism and its
native Picard pullback, on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

namespace Construction

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters

variable {S : Scheme} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [Smooth B.hom] [IsProper B.hom] [GeometricallyConnected B.hom]
    (DA : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (DB : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)
    (ellA : A ⟶ DA.withPicardGroup.abelian) [IsMonHom ellA]
    [IsFinite ellA.left] [Flat ellA.left] [Surjective ellA.left]
    (ellB : B ⟶ DB.withPicardGroup.abelian) [IsMonHom ellB]
    [IsFinite ellB.left] [Flat ellB.left] [Surjective ellB.left]
    (n : ℕ) (hn : 0 < n)
    [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] [Flat ((𝟙 A : A ⟶ A) ^ n).left]
    [Surjective ((𝟙 A : A ⟶ A) ^ n).left] [LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left]
    [IsFinite ((𝟙 B : B ⟶ B) ^ n).left] [Flat ((𝟙 B : B ⟶ B) ^ n).left]
    [Surjective ((𝟙 B : B ⟶ B) ^ n).left] [LocallyOfFinitePresentation ((𝟙 B : B ⟶ B) ^ n).left]
    (CA : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))
    (CB : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 B) ^ n))))
    (f : A ⟶ B) [IsMonHom f]

theorem nativeTorsionCartierIso_morphism :
    (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map
        (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom A B f)) n).op ≫
        (CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso A DA ellA n hn CA).hom =
      (CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso B DB ellB n hn CB).hom ≫
        CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap
          (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicCartierNaturality.Construction.nativePicardPullbackGroup A B f DA.withPicardGroup DB.withPicardGroup)) n :=
  MorphismSquares.Construction.morphismSquare_comp _ _ _
    ((CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk B) n).hom.op)
    ((CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom.op)
    (CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf ((𝟙 B) ^ n) DB.withPicardGroup CB n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow B n))
    (CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf ((𝟙 A) ^ n) DA.withPicardGroup CA n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n))
    (MorphismSquares.Construction.morphismSquare_op_map (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S) _ _ _ _
      (IntrinsicMultiplicationNaturality.Construction.nativeMultiplicationKernelSheafIso_morphism A B f n))
    (IntrinsicCartierSheafNaturality.Construction.nativeCartierTorsionSheaf_natural A B f n DA.withPicardGroup DB.withPicardGroup CA CB)

theorem nativeWeilCharacter_morphism :
    CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap
        (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicCartierNaturality.Construction.nativePicardPullbackGroup A B f DA.withPicardGroup DB.withPicardGroup)) n ≫
        (CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso A DA ellA n hn CA).inv =
      (CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso B DB ellB n hn CB).inv ≫
        (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map
          (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom A B f)) n).op :=
  MorphismSquares.Construction.morphismSquare_inverse (CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso B DB ellB n hn CB)
    (CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso A DA ellA n hn CA) _ _
    (nativeTorsionCartierIso_morphism A B DA DB ellA ellB n hn CA CB f)

theorem nativeWeilPairing_morphism (T : Over S)
    (x : (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n).obj.obj (.op T))
    (y : (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk DB.withPicardGroup.abelian)) n).obj.obj (.op T)) :
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk B)) n) T
      ((CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing B DB ellB n hn CB).rightAdjoint.hom.app (.op T) y)
      ((CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom A B f)) n).hom.app (.op T) x) =
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n) T
      ((CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing A DA ellA n hn CA).rightAdjoint.hom.app (.op T)
        ((CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap
          (IntrinsicCartierNaturality.Construction.nativePicardPullbackGroup A B f DA.withPicardGroup DB.withPicardGroup)) n).hom.app (.op T) y)) x := by
  rw [CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing_rightAdjoint, CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing_rightAdjoint]
  have h := congrArg (fun g => g.hom.app (.op T) y)
    (nativeWeilCharacter_morphism A B DA DB ellA ellB n hn CA CB f)
  exact (CartierDuality.SheafEvaluation.Construction.Schemes.cartierDualSheafMap_value
    (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom A B f)) n)
    T ((CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso B DB ellB n hn CB).inv.hom.app (.op T) y) x).symm.trans
      (congrArg (fun z => CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n) T z x) h.symm)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilNaturality
