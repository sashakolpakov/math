import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ParameterFamilyMaps
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CharacterCoverRefinement
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualPullback

/-! # Character Dual Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CharacterDualPullback

noncomputable section

/-! The actual character descended along a commuting square represents
the original Picard dual pullback of its character-line point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard

universe u
variable {S : Scheme.{u}} {A B A' B' : Over S}
  [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
  (f : A ⟶ B) (f' : A' ⟶ B') [IsMonHom f] [IsMonHom f']
  (s : B' ⟶ B) (t : A' ⟶ A) [IsMonHom s] [IsMonHom t] (w : t ≫ f = f' ≫ s)
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  [IsAffineHom f'.left] [Flat f'.left] [Surjective f'.left] [LocallyOfFinitePresentation f'.left]
  (Q : Over S) (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

omit [LocallyOfFinitePresentation f.left] [LocallyOfFinitePresentation f'.left] in
theorem parameterCharacterLineClass_square :
    (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf s).app (.op Q) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B Q (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)) =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B' Q (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f' Q (ParameterCharacterSquares.squareCharacterSection f f' s t w Q χ)) := by
  have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map s).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f' Q (ParameterCharacterSquares.squareCharacterSection f f' s t w Q χ)) :=
    Quotient.sound (CharacterCoverRefinement.parameterCharacterLine_square f f' s t w Q χ)
  exact (ParameterFamilyMaps.parameterLineClass_groupMap s Q (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)).trans
    (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B' Q)) he)

theorem parameterCharacterHomogeneousClass_square :
    (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf B' B s).app (.op Q) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f Q χ) =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f' Q (ParameterCharacterSquares.squareCharacterSection f f' s t w Q χ) := by
  apply Subtype.ext
  exact (congrArg ((Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf s).app (.op Q))
    (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val f Q χ)).trans
    ((parameterCharacterLineClass_square f f' s t w Q χ).trans
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val f' Q (ParameterCharacterSquares.squareCharacterSection f f' s t w Q χ)).symm)

theorem parameterCharacterPicardHom_square :
    (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback B' B s).hom.app (.op Q) (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f Q χ) =
      CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f' Q (ParameterCharacterSquares.squareCharacterSection f f' s t w Q χ) := by
  have hn := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (Scheme.fppfTopology.over S)
      (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf B' B s)) (.op Q)) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f Q χ)
  exact hn.symm.trans (congrArg
    ((toSheafify (Scheme.fppfTopology.over S) (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B')).app (.op Q))
      (parameterCharacterHomogeneousClass_square f f' s t w Q χ))

theorem parameterCharacterDualPoint_square (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (D' : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B') :
    CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f Q χ D ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D' D s =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f' Q (ParameterCharacterSquares.squareCharacterSection f f' s t w Q χ) D' := by
  apply D'.representable.homEquiv.injective
  have h₁ : D.representable.homEquiv (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f Q χ D) =
      CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f Q χ := D.representable.homEquiv.apply_symm_apply _
  have h₂ : D'.representable.homEquiv
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f' Q (ParameterCharacterSquares.squareCharacterSection f f' s t w Q χ) D') =
        CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f' Q (ParameterCharacterSquares.squareCharacterSection f f' s t w Q χ) :=
    D'.representable.homEquiv.apply_symm_apply _
  exact (Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback_representation D' D s (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f Q χ D)).trans
    ((congrArg ((Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback B' B s).hom.app (.op Q)) h₁).trans
      ((parameterCharacterPicardHom_square f f' s t w Q χ).trans h₂.symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CharacterDualPullback
