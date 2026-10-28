import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCartierNaturality
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardSheaf
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Intertwining

/-! # Intrinsic Cartier Sheaf Source -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCartierSheafSource

noncomputable section

/-! Source naturality of character-line descent on the actual torsion
fppf sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

namespace Construction

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters

theorem nativeCartierRepresentation_natural {S : Scheme} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X]
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (D : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S H)
    (f : H ⟶ G) :
    letI : IsCommMonObj C.dual.X := C.commutative
    letI : IsCommMonObj D.dual.X := D.commutative
    CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (C.dualMap D f) ≫ D.representedCartierDualIso.hom =
      C.representedCartierDualIso.hom ≫
        (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f).op := by
  have : IsCommMonObj C.dual.X := C.commutative
  have : IsCommMonObj D.dual.X := D.commutative
  apply CartierDuality.SheafEvaluation.Construction.Schemes.sheafDualHom_ext
  intro T d x
  exact (D.representedCartierDualIso_value T
      (d.down ≫ (C.dualMap D f).hom.hom) x.down).trans
    ((congrArg ULift.up (C.dualMap_evaluation D f T d.down x.down)).trans
      (C.representedCartierDualIso_value T d.down (x.down ≫ f.hom.hom)).symm)

variable {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]
variable (p : A ⟶ A) [IsMonHom p] (n : ℕ) (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A)
variable [IsAffineHom ((𝟙 A : A ⟶ A) ^ n).left]
variable [Flat ((𝟙 A : A ⟶ A) ^ n).left] [Surjective ((𝟙 A : A ⟶ A) ^ n).left]
variable [LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left]
variable (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))

theorem nativeCartierTorsionSheaf_endomorphism :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map
        (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicCartierNaturality.Construction.nativeMultiplicationKernelMap A p n)).op ≫
        CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf ((𝟙 A) ^ n) D C n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) =
      CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf ((𝟙 A) ^ n) D C n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) ≫
        CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicCartierNaturality.Construction.nativePicardEndomorphismGroup A p D)) n := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  have : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
  have : IsCommMonObj C.dual.X := C.commutative
  let a := C.dualMap C (IntrinsicCartierNaturality.Construction.nativeMultiplicationKernelMap A p n)
  let b := CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionGroupMap (IntrinsicCartierNaturality.Construction.nativePicardEndomorphismGroup A p D) n
  let c := CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup ((𝟙 A) ^ n) D C n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)
  have hc : CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a ≫ CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap c =
      CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap c ≫ CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap b :=
    (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp a c).symm.trans
      ((congrArg (fun f => CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f) (IntrinsicCartierNaturality.Construction.nativeCartierTorsion_endomorphism A p n D C)).trans
        (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp c b))
  exact Intertwining.Construction.intertwining_sourceIso C.representedCartierDualIso (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a) _ _
    (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap c ≫ (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk D.abelian) n).hom)
    (nativeCartierRepresentation_natural C C (IntrinsicCartierNaturality.Construction.nativeMultiplicationKernelMap A p n))
    (Intertwining.Construction.intertwining_comp _ (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap b) _ _ _ hc
      (CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionSheafIso_natural (IntrinsicCartierNaturality.Construction.nativePicardEndomorphismGroup A p D) n))

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCartierSheafSource
