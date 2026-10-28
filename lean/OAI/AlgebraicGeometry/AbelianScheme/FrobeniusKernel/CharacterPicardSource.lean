import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterCharacterLineSource
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterFamilySource
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterLineNaturality
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousPullback

/-! # Character Picard Source -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterPicardSource.Construction

noncomputable section

/-! The canonical character-line construction intertwines original
source pullback on the genuine relative and homogeneous Picard sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] BaseChange.Construction.pulledBackGroup

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterLineNaturality.Construction.KernelCharacters

variable {S : Scheme} {A B A' B' : Over S}
variable [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
variable (f : A ⟶ B) (f' : A' ⟶ B') [IsMonHom f] [IsMonHom f']
variable (a : A' ⟶ A) (b : B' ⟶ B) [IsMonHom a] [IsMonHom b]
variable (h : a ≫ f = f' ≫ b)
variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
variable [IsAffineHom f'.left] [Flat f'.left] [Surjective f'.left] [LocallyOfFinitePresentation f'.left]
variable (Q : Over S) (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

omit [LocallyOfFinitePresentation f.left] [LocallyOfFinitePresentation f'.left] in
theorem parameterCharacterLine_class_source :
    (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf b).app (.op Q) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B Q (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)) =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B' Q (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f' Q (ParameterCharacterSourceRestriction.Construction.parameterSourceRestrictedCharacter f f' a b h Q χ)) := by
  have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map b).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f' Q (ParameterCharacterSourceRestriction.Construction.parameterSourceRestrictedCharacter f f' a b h Q χ)) :=
    Quotient.sound (ParameterCharacterLineSource.Construction.parameterCharacterLine_sourceSquare f f' a b h Q χ)
  exact (ParameterFamilySource.Construction.parameterLineClass_sourcePullback b Q (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)).trans
    (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B' Q)) he)

theorem parameterCharacterHomogeneousClass_source :
    (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf B' B b).app (.op Q) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f Q χ) =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f' Q (ParameterCharacterSourceRestriction.Construction.parameterSourceRestrictedCharacter f f' a b h Q χ) := by
  apply Subtype.ext
  exact (congrArg ((Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf b).app (.op Q))
    (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val f Q χ)).trans
      ((parameterCharacterLine_class_source f f' a b h Q χ).trans
        (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val f' Q (ParameterCharacterSourceRestriction.Construction.parameterSourceRestrictedCharacter f f' a b h Q χ)).symm)

theorem parameterCharacterPicardHom_source :
    (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback B' B b).hom.app (.op Q) (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f Q χ) =
      CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f' Q (ParameterCharacterSourceRestriction.Construction.parameterSourceRestrictedCharacter f f' a b h Q χ) := by
  have hn := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (Scheme.fppfTopology.over S)
      (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf B' B b)) (.op Q)) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f Q χ)
  exact hn.symm.trans (congrArg
    ((toSheafify (Scheme.fppfTopology.over S) (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B')).app (.op Q))
      (parameterCharacterHomogeneousClass_source f f' a b h Q χ))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterPicardSource.Construction
