import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterPicard
import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualHomomorphism
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CommutativeSheavesAb
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CommGroupTypeMap

/-! # Picard Commutative Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction

noncomputable section

/-! The existing homogeneous Picard sheaf, with its tensor-product
group law, as an object of the actual commutative fppf-sheaf category. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.Homomorphisms.DualHomomorphism.Construction

variable {S : Scheme.{u}} {g h : ℕ}

def homogeneousPicardFppfAb (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S :=
  ⟨Picard.Homomorphisms.GroupFunctor.Construction.homogeneousPicardGroupFunctor A,
    Presheaf.isSheaf_of_isSheaf_comp (Scheme.fppfTopology.over S)
      (Picard.Homomorphisms.GroupFunctor.Construction.homogeneousPicardGroupFunctor A) (forget CommGrpCat.{u + 1})
      ((Presheaf.isSheaf_of_iso_iff (J := Scheme.fppfTopology.over S)
        (Picard.Homomorphisms.GroupFunctor.Construction.homogeneousPicardGroupForgetIso A)).mpr A.homogeneousPicardSheaf.property)⟩

def homogeneousPicardFppfAb_typeIso (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) :
    (sheafCompose (Scheme.fppfTopology.over S) (forget CommGrpCat.{u + 1})).obj
      (homogeneousPicardFppfAb A) ≅ A.homogeneousPicardSheaf :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (Picard.Homomorphisms.GroupFunctor.Construction.homogeneousPicardGroupForgetIso A)

variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]

def homogeneousPicardFppfPullback : homogeneousPicardFppfAb B ⟶ homogeneousPicardFppfAb A where
  hom := CommGroupTypeMap.Construction.commGroupNatTransOfType (Picard.Homomorphisms.GroupFunctor.Construction.homogeneousPicardGroupForgetIso B)
    (Picard.Homomorphisms.GroupFunctor.Construction.homogeneousPicardGroupForgetIso A) (Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullback A B f).hom
    (fun T => Picard.Homomorphisms.DualHomomorphism.Construction.homogeneousPicardPullbackHom A B f T.unop)
    (fun T c => Picard.Homomorphisms.DualHomomorphism.Construction.homogeneousPicardPullbackHom_apply A B f T.unop c)

theorem homogeneousPicardFppfPullback_apply (T : Over S)
    (c : B.homogeneousPicardSheaf.obj.obj (.op T)) :
    (homogeneousPicardFppfPullback A B f).hom.app (.op T) c =
      (Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullback A B f).hom.app (.op T) c :=
  Picard.Homomorphisms.DualHomomorphism.Construction.homogeneousPicardPullbackHom_apply A B f T c

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left]

def characterToPicardFppfAb : CartierDuality.CharacterGroupSheaf.Construction.Schemes.characterCommGroupSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) ⟶
    homogeneousPicardFppfAb B where
  hom := CommGroupTypeMap.Construction.commGroupNatTransOfType (Iso.refl _) (Picard.Homomorphisms.GroupFunctor.Construction.homogeneousPicardGroupForgetIso B)
    (CartierDuality.PicardMonomorphism.Construction.KernelCharacters.characterToPicardTypeSheafMap f).hom (fun T => CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T.unop)
    (fun _ _ => rfl)

theorem characterToPicardFppfAb_apply (T : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op T)) :
    (characterToPicardFppfAb A B f).hom.app (.op T) χ = CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T χ := rfl

theorem characterToPicardFppfAb_pullback :
    characterToPicardFppfAb A B f ≫ homogeneousPicardFppfPullback A B f = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro χ
  exact (homogeneousPicardFppfPullback_apply A B f T.unop _).trans
    ((CharacterPicard.Construction.parameterCharacterPicardHom_pullback f T.unop χ).trans
      (Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.trivialHomogeneousPicardClass_eq_one A.scheme T.unop))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction
