import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCartierNaturality
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCartierSheafSource
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.MorphismSquares

/-! # Intrinsic Cartier Sheaf Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCartierSheafNaturality

noncomputable section

/-! Naturality of the canonical Cartier-to-Picard map on torsion sheaves
for maps between two native source groups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

namespace Construction

variable {S : Scheme} (A B : Over S) [GrpObj A] [GrpObj B]
variable [IsCommMonObj A] [IsCommMonObj B]
variable (f : A ⟶ B) [IsMonHom f] (n : ℕ) (DA : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (DB : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)
variable [IsAffineHom ((𝟙 A : A ⟶ A) ^ n).left]
variable [Flat ((𝟙 A : A ⟶ A) ^ n).left] [Surjective ((𝟙 A : A ⟶ A) ^ n).left]
variable [LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left]
variable [IsAffineHom ((𝟙 B : B ⟶ B) ^ n).left]
variable [Flat ((𝟙 B : B ⟶ B) ^ n).left] [Surjective ((𝟙 B : B ⟶ B) ^ n).left]
variable [LocallyOfFinitePresentation ((𝟙 B : B ⟶ B) ^ n).left]
variable (CA : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))
variable (CB : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 B) ^ n))))

theorem nativeCartierTorsionSheaf_natural :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup DA
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup DB
    letI : IsCommMonObj DA.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative DA
    letI : IsCommMonObj DB.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative DB
    (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map
        (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicCartierNaturality.Construction.nativeMultiplicationKernelHom A B f n)).op ≫
        CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf ((𝟙 A) ^ n) DA CA n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) =
      CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf ((𝟙 B) ^ n) DB CB n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow B n) ≫
        CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicCartierNaturality.Construction.nativePicardPullbackGroup A B f DA DB)) n := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup DA
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup DB
  have : IsCommMonObj DA.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative DA
  have : IsCommMonObj DB.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative DB
  have : IsCommMonObj CA.dual.X := CA.commutative
  have : IsCommMonObj CB.dual.X := CB.commutative
  let a := CB.dualMap CA (IntrinsicCartierNaturality.Construction.nativeMultiplicationKernelHom A B f n)
  let b := CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionGroupMap (IntrinsicCartierNaturality.Construction.nativePicardPullbackGroup A B f DA DB) n
  let cA := CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup ((𝟙 A) ^ n) DA CA n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)
  let cB := CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup ((𝟙 B) ^ n) DB CB n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow B n)
  have hc : CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a ≫ CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap cA =
      CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap cB ≫ CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap b :=
    (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp a cA).symm.trans
      ((congrArg (fun h => CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap h) (IntrinsicCartierNaturality.Construction.nativeCartierTorsion_natural A B f n DA DB CA CB)).trans
        (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp cB b))
  exact MorphismSquares.Construction.morphismSquare_sourceIso CB.representedCartierDualIso CA.representedCartierDualIso
    (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a) _ _
    (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap cB ≫ (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk DB.abelian) n).hom)
    (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap cA ≫ (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk DA.abelian) n).hom)
    (IntrinsicCartierSheafSource.Construction.nativeCartierRepresentation_natural CB CA (IntrinsicCartierNaturality.Construction.nativeMultiplicationKernelHom A B f n))
    (MorphismSquares.Construction.morphismSquare_comp _ (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap b) _ _ _ _ _ hc
      (CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionSheafIso_natural (IntrinsicCartierNaturality.Construction.nativePicardPullbackGroup A B f DA DB) n))

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCartierSheafNaturality
