import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCharacterRestrictionEpi
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterPicardSource

/-! # Picard Character Source Square -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCharacterSourceSquare.Construction

noncomputable section

/-! Source-square compatibility for the actual character-line maps into
commutative Picard sheaves, before a dual of the target is constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} {g h g' h' : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
  (A' : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g' S) (B' : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h' S)
variable (f : A.scheme ⟶ B.scheme) (f' : A'.scheme ⟶ B'.scheme) [IsMonHom f] [IsMonHom f']
variable (a : A'.scheme ⟶ A.scheme) (b : B'.scheme ⟶ B.scheme) [IsMonHom a] [IsMonHom b]
variable (w : a ≫ f = f' ≫ b)
variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
variable [IsAffineHom f'.left] [Flat f'.left] [Surjective f'.left] [LocallyOfFinitePresentation f'.left]

theorem characterToPicardFppfAb_source :
    PicardCommutativeSheaf.Construction.characterToPicardFppfAb A B f ≫ PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback B' B b =
      IntrinsicCharacterRestrictionEpi.Construction.nativeCharacterRestriction (ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap f f' a b w) ≫
        PicardCommutativeSheaf.Construction.characterToPicardFppfAb A' B' f' := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro χ
  change Picard.Homomorphisms.DualHomomorphism.Construction.homogeneousPicardPullbackHom B' B b T.unop (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T.unop χ) = _
  exact (Picard.Homomorphisms.DualHomomorphism.Construction.homogeneousPicardPullbackHom_apply B' B b T.unop
    (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T.unop χ)).trans
      (CharacterPicardSource.Construction.parameterCharacterPicardHom_source f f' a b w T.unop χ)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCharacterSourceSquare.Construction
