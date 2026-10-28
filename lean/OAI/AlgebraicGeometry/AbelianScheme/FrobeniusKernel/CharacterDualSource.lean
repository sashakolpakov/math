import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterPicardSource
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualPullback
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardHomomorphism
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentationMorphisms

/-! # Character Dual Source -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterDualSource.Construction

noncomputable section

/-! Actual character descent intertwines a source group map and its
canonical Picard dual. The map on characters is the original restriction
through the scheme-kernel square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardHomomorphism.Construction.KernelCharacters

variable {S : Scheme} {A B A' B' : Over S}
variable [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
variable (f : A ⟶ B) (f' : A' ⟶ B') [IsMonHom f] [IsMonHom f']
variable (a : A' ⟶ A) (b : B' ⟶ B) [IsMonHom a] [IsMonHom b]
variable (h : a ≫ f = f' ≫ b)
variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
variable [IsAffineHom f'.left] [Flat f'.left] [Surjective f'.left] [LocallyOfFinitePresentation f'.left]
variable (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (D' : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B')

theorem parameterCharacterDualPoint_source (Q : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q)) :
    CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f Q χ D ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D' D b =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f' Q (ParameterCharacterSourceRestriction.Construction.parameterSourceRestrictedCharacter f f' a b h Q χ) D' := by
  apply D'.representable.homEquiv.injective
  have h₁ : D.representable.homEquiv (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f Q χ D) =
      CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f Q χ := D.representable.homEquiv.apply_symm_apply _
  have h₂ : D'.representable.homEquiv
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f' Q (ParameterCharacterSourceRestriction.Construction.parameterSourceRestrictedCharacter f f' a b h Q χ) D') =
      CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f' Q (ParameterCharacterSourceRestriction.Construction.parameterSourceRestrictedCharacter f f' a b h Q χ) :=
    D'.representable.homEquiv.apply_symm_apply _
  exact (Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback_representation D' D b (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f Q χ D)).trans
    ((congrArg ((Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback B' B b).hom.app (.op Q)) h₁).trans
      ((CharacterPicardSource.Construction.parameterCharacterPicardHom_source f f' a b h Q χ).trans h₂.symm))

variable (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
variable (C' : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f')))

theorem canonicalCartierPicardMap_source :
    (C.dualMap C' (ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap f f' a b h)).hom.hom ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f' D' C' =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D' D b := by
  have hc := C.dualMap_character C' (ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap f f' a b h) C.dual.X (𝟙 C.dual.X)
  rw [Category.id_comp] at hc
  exact (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply f' D' C' C.dual.X
    (C.dualMap C' (ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap f f' a b h)).hom.hom).trans
      ((congrArg (fun χ => CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f' C.dual.X χ D') hc).trans
        (parameterCharacterDualPoint_source f f' a b h D D' C.dual.X
          (C.sectionEquiv C.dual.X (𝟙 C.dual.X))).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterDualSource.Construction
