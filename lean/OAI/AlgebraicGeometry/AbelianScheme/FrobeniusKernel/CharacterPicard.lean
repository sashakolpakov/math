import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousPullback

/-! # Character Picard -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterPicard.Construction

noncomputable section

/-! Character descent lands in the kernel of actual homogeneous Picard
pullback, on every parameter scheme and without a dual for the quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard
open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism.Construction.KernelCharacters

variable {S : Scheme.{u}} {A B : Over S}

theorem characterParameterFamilyMap_square (f : A ⟶ B) (Q : Over S) :
    (Q ◁ f).left ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A Q ≫ ((Over.pullback Q.hom).map f).left := by
  have hfst : ((Over.pullback Q.hom).map f).left ≫ pullback.fst B.hom Q.hom =
      pullback.fst A.hom Q.hom ≫ f.left := pullback.lift_fst _ _ _
  have hsnd : ((Over.pullback Q.hom).map f).left ≫ pullback.snd B.hom Q.hom =
      pullback.snd A.hom Q.hom := pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · rw [Category.assoc, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_fst]
    rw [Category.assoc, hfst,
      ← Category.assoc, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_fst]
    exact congrArg Over.Hom.left (whiskerLeft_snd Q f)
  · rw [Category.assoc, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_snd]
    rw [Category.assoc, hsnd,
      CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_snd]
    exact congrArg Over.Hom.left (whiskerLeft_fst Q f)

variable [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left]
variable (Q : Over S)
variable (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

omit [LocallyOfFinitePresentation f.left] in
theorem parameterCharacterLine_pullback_trivial :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Q ◁ f).left
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B Q (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (Q ⊗ A).left := by
  have : IsAffineHom ((Over.pullback Q.hom).map f).left :=
    (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).1
  have : Flat ((Over.pullback Q.hom).map f).left :=
    (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.1
  have : Surjective ((Over.pullback Q.hom).map f).left :=
    (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.2
  have hline : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.pullback Q.hom).obj A).left :=
    Quotient.sound ⟨CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLineFrame ((Over.pullback Q.hom).map f)
      (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ) (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ)⟩
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Q ◁ f).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ))) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, characterParameterFamilyMap_square,
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, hline, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]

theorem parameterCharacterHomogeneousClass_pullback :
    (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf A B f).app (.op Q)
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f Q χ) =
        ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass _, Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.trivialClass_homogeneous A Q⟩ := by
  apply Subtype.ext
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Q ◁ f).left
    (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f Q χ).val = _
  rw [CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val]
  exact parameterCharacterLine_pullback_trivial f Q χ

theorem parameterCharacterPicardHom_pullback :
    (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (.op Q)
      (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f Q χ) = Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass A Q := by
  have hn := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (Scheme.fppfTopology.over S)
      (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf A B f)) (.op Q))
    (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f Q χ)
  exact hn.symm.trans (congrArg
    ((toSheafify (Scheme.fppfTopology.over S) (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)).app (.op Q))
    (parameterCharacterHomogeneousClass_pullback f Q χ))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterPicard.Construction
