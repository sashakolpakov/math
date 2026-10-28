import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ParameterCharacterSquares

/-! # Character Cover Refinement -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CharacterCoverRefinement

noncomputable section

/-! Refining a multiplication cover preserves the actual Picard point
of the restricted character. This is the line-descent comparison needed
for compatibility of canonical Weil pairings at different levels. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
section Square
variable {S : Scheme.{u}} {A B A' B' : Over S}
  [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
  (f : A ⟶ B) (f' : A' ⟶ B') [IsMonHom f] [IsMonHom f']
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsAffineHom f'.left] [Flat f'.left] [Surjective f'.left]
  (s : B' ⟶ B) (t : A' ⟶ A) [IsMonHom s] [IsMonHom t]
  (w : t ≫ f = f' ≫ s) (Q : Over S)
  (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

theorem parameterCharacterLine_square :
    Nonempty ((Scheme.Modules.pullback ((Over.pullback Q.hom).map s).left).obj
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ).sheaf ≅
        (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f' Q (ParameterCharacterSquares.squareCharacterSection f f' s t w Q χ)).sheaf) := by
  have ha : IsAffineHom ((Over.pullback Q.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).1
  have hf : Flat ((Over.pullback Q.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.1
  have hs : Surjective ((Over.pullback Q.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.2
  have ha' : IsAffineHom ((Over.pullback Q.hom).map f').left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f').1
  have hf' : Flat ((Over.pullback Q.hom).map f').left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f').2.1
  have hs' : Surjective ((Over.pullback Q.hom).map f').left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f').2.2
  obtain ⟨e⟩ := KernelCharacterSquares.characterDescendedLine_square ((Over.pullback Q.hom).map f) ((Over.pullback Q.hom).map f')
    ((Over.pullback Q.hom).map s) ((Over.pullback Q.hom).map t) (ParameterCharacterSquares.square_pullback f f' s t w Q)
    (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ) (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ)
  have he := CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.characterDescendedLine_congr ((Over.pullback Q.hom).map f')
    (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f' Q (ParameterCharacterSquares.squareCharacterSection f f' s t w Q χ))
    (KernelCharacterSquares.squareKernelCharacter ((Over.pullback Q.hom).map f) ((Over.pullback Q.hom).map f')
      ((Over.pullback Q.hom).map s) ((Over.pullback Q.hom).map t) (ParameterCharacterSquares.square_pullback f f' s t w Q)
        (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ))
    (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f' Q (ParameterCharacterSquares.squareCharacterSection f f' s t w Q χ))
    (KernelCharacterSquares.squareKernelCharacter_natural ((Over.pullback Q.hom).map f) ((Over.pullback Q.hom).map f')
      ((Over.pullback Q.hom).map s) ((Over.pullback Q.hom).map t) (ParameterCharacterSquares.square_pullback f f' s t w Q)
      (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ) (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ))
    (funext fun U => MonoidHom.ext fun x => ParameterCharacterSquares.parameterKernelCharacter_square f f' s t w Q χ U x)
  exact ⟨e ≪≫ eqToIso (congrArg AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.sheaf he.symm)⟩

end Square

variable {S : Scheme.{u}} {A B A' : Over S}
  [GrpObj A] [GrpObj B] [GrpObj A']
  (f : A ⟶ B) (f' : A' ⟶ B) [IsMonHom f] [IsMonHom f']
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsAffineHom f'.left] [Flat f'.left] [Surjective f'.left]
  (t : A' ⟶ A) [IsMonHom t] (w : t ≫ f = f') (Q : Over S)
  (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

def refinementCharacterSection :=
  ParameterCharacterSquares.squareCharacterSection f f' (𝟙 B) t (w.trans (Category.comp_id f').symm) Q χ

theorem parameterCharacterLine_refinement :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f' Q (refinementCharacterSection f f' t w Q χ)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ) := by
  have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map (𝟙 B)).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f' Q (refinementCharacterSection f f' t w Q χ)) :=
    Quotient.sound (parameterCharacterLine_square f f' (𝟙 B) t
      (w.trans (Category.comp_id f').symm) Q χ)
  have hi : ((Over.pullback Q.hom).map (𝟙 B)).left = 𝟙 ((Over.pullback Q.hom).obj B).left :=
    congrArg Over.Hom.left ((Over.pullback Q.hom).map_id B)
  exact h.symm.trans ((congrArg (fun a => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ))) hi).trans (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id _))

variable [LocallyOfFinitePresentation f.left] [LocallyOfFinitePresentation f'.left]

theorem parameterCharacterHomogeneousClass_refinement :
    CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f' Q (refinementCharacterSection f f' t w Q χ) =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f Q χ := by
  apply Subtype.ext
  rw [CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val, CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val]
  exact congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q))
    (parameterCharacterLine_refinement f f' t w Q χ)

theorem parameterCharacterDualPoint_refinement (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) :
    CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f' Q (refinementCharacterSection f f' t w Q χ) D =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f Q χ D := by
  unfold CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint
  rw [parameterCharacterHomogeneousClass_refinement]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CharacterCoverRefinement
