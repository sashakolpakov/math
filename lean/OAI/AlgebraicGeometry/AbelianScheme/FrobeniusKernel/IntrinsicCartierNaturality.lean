import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicPicardHomomorphism
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterDualSource
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafTorsionMaps

/-! # Intrinsic Cartier Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCartierNaturality

noncomputable section

section

/-! Endomorphism naturality of the actual Cartier-to-dual-torsion group
map, entirely in the native Picard group. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

namespace Construction

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes

variable {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]
variable (p : A ⟶ A) [IsMonHom p] (n : ℕ)

omit [IsCommMonObj A] in
theorem nativeEndomorphism_multiplication : p ≫ ((𝟙 A) ^ n) = ((𝟙 A) ^ n) ≫ p := by
  rw [MonObj.comp_pow, MonObj.pow_comp, Category.comp_id, Category.id_comp]

def nativeMultiplicationKernelMap :
    Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)) ⟶ Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)) :=
  ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap ((𝟙 A) ^ n) ((𝟙 A) ^ n) p p (nativeEndomorphism_multiplication A p n)

variable (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A)

def nativePicardEndomorphismGroup :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    Grp.mk D.abelian ⟶ Grp.mk D.abelian :=
  letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  @Grp.homMk (Over S) _ _ (Grp.mk D.abelian) (Grp.mk D.abelian)
    (Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D D p) (IntrinsicPicardHomomorphism.Construction.IntrinsicPicard.dualPullback_isMonHom p D D)

variable [IsAffineHom ((𝟙 A : A ⟶ A) ^ n).left]
variable [Flat ((𝟙 A : A ⟶ A) ^ n).left] [Surjective ((𝟙 A : A ⟶ A) ^ n).left]
variable [LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left]
variable (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))

theorem nativeCartierPicard_endomorphism :
    (C.dualMap C (nativeMultiplicationKernelMap A p n)).hom.hom ≫
        CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((𝟙 A) ^ n) D C =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((𝟙 A) ^ n) D C ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D D p :=
  CharacterDualSource.Construction.canonicalCartierPicardMap_source ((𝟙 A) ^ n) ((𝟙 A) ^ n) p p
    (nativeEndomorphism_multiplication A p n) D D C C

theorem nativeCartierTorsion_endomorphism :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    C.dualMap C (nativeMultiplicationKernelMap A p n) ≫
        CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup ((𝟙 A) ^ n) D C n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) =
      CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup ((𝟙 A) ^ n) D C n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) ≫
        CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionGroupMap (nativePicardEndomorphismGroup A p D) n := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  have : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
  have : Mono (TorsionQuotient.SubgroupFunctor.torsionι D.abelian n) := inferInstanceAs (Mono (equalizer.ι ((𝟙 D.abelian) ^ n) 1))
  apply Grp.hom_ext
  apply (cancel_mono (TorsionQuotient.SubgroupFunctor.torsionι D.abelian n)).mp
  let c := CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion ((𝟙 A) ^ n) D n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) C
  let d := Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D D p
  have : IsMonHom d := IntrinsicPicardHomomorphism.Construction.IntrinsicPicard.dualPullback_isMonHom p D D
  change ((C.dualMap C (nativeMultiplicationKernelMap A p n)).hom.hom ≫ c) ≫ TorsionQuotient.SubgroupFunctor.torsionι D.abelian n =
    (c ≫ CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap d n) ≫ TorsionQuotient.SubgroupFunctor.torsionι D.abelian n
  rw [Category.assoc, Category.assoc, CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap_inclusion]
  rw [show c ≫ TorsionQuotient.SubgroupFunctor.torsionι D.abelian n = CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((𝟙 A) ^ n) D C from
    CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion_inclusion ((𝟙 A) ^ n) D n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) C]
  rw [← Category.assoc c (TorsionQuotient.SubgroupFunctor.torsionι D.abelian n) d]
  rw [show c ≫ TorsionQuotient.SubgroupFunctor.torsionι D.abelian n = CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((𝟙 A) ^ n) D C from
    CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion_inclusion ((𝟙 A) ^ n) D n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) C]
  exact nativeCartierPicard_endomorphism A p n D C

end Construction

end

/-! Naturality of actual Cartier character-line descent for a morphism
between two source groups and their native Picard duals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

namespace Construction

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes

variable {S : Scheme} (A B : Over S) [GrpObj A] [GrpObj B]
variable (f : A ⟶ B) [IsMonHom f] (n : ℕ)

theorem nativeGroupMultiplication_natural :
    f ≫ ((𝟙 B) ^ n) = ((𝟙 A) ^ n) ≫ f := by
  rw [MonObj.comp_pow, MonObj.pow_comp, Category.comp_id, Category.id_comp]

variable [IsCommMonObj A] [IsCommMonObj B]

def nativeMultiplicationKernelHom :
    Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)) ⟶ Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 B) ^ n)) :=
  ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap ((𝟙 B) ^ n) ((𝟙 A) ^ n) f f
    (nativeGroupMultiplication_natural A B f n)

variable (DA : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (DB : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)

def nativePicardPullbackGroup :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup DA
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup DB
    Grp.mk DB.abelian ⟶ Grp.mk DA.abelian :=
  letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup DA
  letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup DB
  @Grp.homMk (Over S) _ _ (Grp.mk DB.abelian) (Grp.mk DA.abelian)
    (Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback DA DB f) (IntrinsicPicardHomomorphism.Construction.IntrinsicPicard.dualPullback_isMonHom f DA DB)

variable [IsAffineHom ((𝟙 A : A ⟶ A) ^ n).left]
variable [Flat ((𝟙 A : A ⟶ A) ^ n).left] [Surjective ((𝟙 A : A ⟶ A) ^ n).left]
variable [LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left]
variable [IsAffineHom ((𝟙 B : B ⟶ B) ^ n).left]
variable [Flat ((𝟙 B : B ⟶ B) ^ n).left] [Surjective ((𝟙 B : B ⟶ B) ^ n).left]
variable [LocallyOfFinitePresentation ((𝟙 B : B ⟶ B) ^ n).left]
variable (CA : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))
variable (CB : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 B) ^ n))))

theorem nativeCartierPicard_natural :
    (CB.dualMap CA (nativeMultiplicationKernelHom A B f n)).hom.hom ≫
        CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((𝟙 A) ^ n) DA CA =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((𝟙 B) ^ n) DB CB ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback DA DB f :=
  CharacterDualSource.Construction.canonicalCartierPicardMap_source ((𝟙 B) ^ n) ((𝟙 A) ^ n) f f
    (nativeGroupMultiplication_natural A B f n) DB DA CB CA

theorem nativeCartierTorsion_natural :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup DA
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup DB
    letI : IsCommMonObj DA.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative DA
    letI : IsCommMonObj DB.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative DB
    CB.dualMap CA (nativeMultiplicationKernelHom A B f n) ≫
        CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup ((𝟙 A) ^ n) DA CA n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) =
      CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup ((𝟙 B) ^ n) DB CB n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow B n) ≫
        CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionGroupMap (nativePicardPullbackGroup A B f DA DB) n := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup DA
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup DB
  have : IsCommMonObj DA.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative DA
  have : IsCommMonObj DB.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative DB
  have : Mono (TorsionQuotient.SubgroupFunctor.torsionι DA.abelian n) :=
    inferInstanceAs (Mono (equalizer.ι ((𝟙 DA.abelian) ^ n) 1))
  apply Grp.hom_ext
  apply (cancel_mono (TorsionQuotient.SubgroupFunctor.torsionι DA.abelian n)).mp
  let a := CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion ((𝟙 A) ^ n) DA n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) CA
  let b := CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion ((𝟙 B) ^ n) DB n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow B n) CB
  let d := Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback DA DB f
  have : IsMonHom d := IntrinsicPicardHomomorphism.Construction.IntrinsicPicard.dualPullback_isMonHom f DA DB
  change ((CB.dualMap CA (nativeMultiplicationKernelHom A B f n)).hom.hom ≫ a) ≫ TorsionQuotient.SubgroupFunctor.torsionι DA.abelian n =
    (b ≫ CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap d n) ≫ TorsionQuotient.SubgroupFunctor.torsionι DA.abelian n
  rw [Category.assoc, Category.assoc, CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap_inclusion]
  rw [show a ≫ TorsionQuotient.SubgroupFunctor.torsionι DA.abelian n = CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((𝟙 A) ^ n) DA CA from
    CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion_inclusion ((𝟙 A) ^ n) DA n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) CA]
  rw [← Category.assoc b (TorsionQuotient.SubgroupFunctor.torsionι DB.abelian n) d]
  rw [show b ≫ TorsionQuotient.SubgroupFunctor.torsionι DB.abelian n = CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((𝟙 B) ^ n) DB CB from
    CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion_inclusion ((𝟙 B) ^ n) DB n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow B n) CB]
  exact nativeCartierPicard_natural A B f n DA DB CA CB

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCartierNaturality
