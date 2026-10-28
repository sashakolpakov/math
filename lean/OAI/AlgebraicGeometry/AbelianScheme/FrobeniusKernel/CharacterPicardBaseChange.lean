import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterLineBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterFamilyBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterLineNaturality
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualBaseChange

/-! # Character Picard Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterPicardBaseChange.Construction

noncomputable section

/-! The canonical parameter character line, its homogeneous Picard
class, and its represented dual point commute with source base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] BaseChange.Construction.pulledBackGroup CharacterLineBaseChange.Construction.parameterChangedCover_affine
  CharacterLineBaseChange.Construction.parameterChangedCover_flat CharacterLineBaseChange.Construction.parameterChangedCover_surjective

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterLineNaturality.Construction.KernelCharacters

variable {S S' : Scheme} (s : S' ⟶ S) (Q : Over S')
variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
variable (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op ((Over.map s).obj Q)))

theorem parameterCharacterLine_class_baseChange :
    (AbelianModuli.HilbertConstruction.Picard.BaseChange.relativePicardPresheafBaseChangeIso B s).hom.app (.op Q)
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass ((Over.pullback s).obj B) Q
        (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine ((Over.pullback s).map f) Q
          (CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f Q χ))) =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B ((Over.map s).obj Q) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f ((Over.map s).obj Q) χ) := by
  have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (ParameterBaseChange.Construction.parameterBaseChangeInv s Q B).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f ((Over.map s).obj Q) χ)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine ((Over.pullback s).map f) Q
        (CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f Q χ)) :=
    Quotient.sound (CharacterLineBaseChange.Construction.parameterCharacterLine_baseChange s Q f χ)
  exact (congrArg (fun z => (AbelianModuli.HilbertConstruction.Picard.BaseChange.relativePicardPresheafBaseChangeIso B s).hom.app (.op Q)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap ((Over.pullback s).obj B) Q) z)) he).symm.trans
    (ParameterFamilyBaseChange.Construction.parameterLineClass_baseChange s Q B (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f ((Over.map s).obj Q) χ))

variable [LocallyOfFinitePresentation f.left]

omit [GrpObj A] [GrpObj B] [IsMonHom f] [IsAffineHom f.left] [Flat f.left] [Surjective f.left] in
local instance parameterChangedCover_presentation :
    LocallyOfFinitePresentation ((Over.pullback s).map f).left :=
  CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.baseChangedCover_locallyOfFinitePresentation f (Over.mk s)

theorem parameterCharacterHomogeneousClass_baseChange :
    (Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardPresheafBaseChangeIso B s).hom.app (.op Q)
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass ((Over.pullback s).map f) Q
        (CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f Q χ)) =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f ((Over.map s).obj Q) χ := by
  apply Subtype.ext
  exact (congrArg ((AbelianModuli.HilbertConstruction.Picard.BaseChange.relativePicardPresheafBaseChangeIso B s).hom.app (.op Q))
    (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val ((Over.pullback s).map f) Q
      (CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f Q χ))).trans
    ((parameterCharacterLine_class_baseChange s Q f χ).trans
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val f ((Over.map s).obj Q) χ).symm)

theorem parameterCharacterPicardHom_baseChange :
    Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardBaseChangeEquiv B s Q
      (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom ((Over.pullback s).map f) Q
        (CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f Q χ)) =
      CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f ((Over.map s).obj Q) χ := by
  exact (Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.toHomogeneousPicard_baseChange_apply B s Q
    (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass ((Over.pullback s).map f) Q
      (CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f Q χ))).trans
    (congrArg ((toSheafify (Scheme.fppfTopology.over S) (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B)).app
      (.op ((Over.map s).obj Q))) (parameterCharacterHomogeneousClass_baseChange s Q f χ))

theorem parameterCharacterDualPoint_baseChange (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) :
    Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D.abelian s Q
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((Over.pullback s).map f) Q
        (CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f Q χ) (D.pullback s)) =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f ((Over.map s).obj Q) χ D := by
  apply D.representable.homEquiv.injective
  have hn : (D.pullback s).representable.homEquiv
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((Over.pullback s).map f) Q
        (CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f Q χ) (D.pullback s)) =
      CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom ((Over.pullback s).map f) Q
        (CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f Q χ) :=
    (D.pullback s).representable.homEquiv.apply_symm_apply _
  have ho : D.representable.homEquiv
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f ((Over.map s).obj Q) χ D) =
      CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f ((Over.map s).obj Q) χ :=
    D.representable.homEquiv.apply_symm_apply _
  exact (D.pullbackRepresentable_comparison s Q _).symm.trans
    ((congrArg (Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardBaseChangeEquiv B s Q) hn).trans
      ((parameterCharacterPicardHom_baseChange s Q f χ).trans ho.symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterPicardBaseChange.Construction
