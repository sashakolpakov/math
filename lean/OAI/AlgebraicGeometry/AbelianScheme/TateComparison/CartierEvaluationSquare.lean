import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CharacterDualPullback
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism

/-! # Cartier Evaluation Square -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CartierEvaluationSquare

noncomputable section

/-! Cartier evaluation respects the actual Picard dual of a commuting
square of group covers, by uniqueness of descended characters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism.Construction.KernelCharacters

universe u
variable {k : Type u} [Field k] {A B A' B' : Over (Spec (.of k))}
  [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
  [Smooth A'.hom] [IsProper A'.hom] [GeometricallyConnected A'.hom]
  (f : A ⟶ B) (f' : A' ⟶ B') [IsMonHom f] [IsMonHom f']
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  [IsAffineHom f'.left] [Flat f'.left] [Surjective f'.left] [LocallyOfFinitePresentation f'.left]
  (s : B' ⟶ B) (t : A' ⟶ A) [IsMonHom s] [IsMonHom t] (w : t ≫ f = f' ≫ s)
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (D' : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B')
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  (C' : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f')))

theorem cartierCharacter_square (Q : Over (Spec (.of k)))
    (z : Q ⟶ C.dual.X) (z' : Q ⟶ C'.dual.X)
    (hz : (z ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C) ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D' D s = z' ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f' D' C') :
    ParameterCharacterSquares.squareCharacterSection f f' s t w Q (C.sectionEquiv Q z) = C'.sectionEquiv Q z' := by
  apply CartierDuality.PicardMonomorphism.Construction.KernelCharacters.parameterCharacterPicardHom_injective f' Q
  have hs := CharacterDualPullback.parameterCharacterDualPoint_square f f' s t w Q (C.sectionEquiv Q z) D D'
  have hp : CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f' Q (ParameterCharacterSquares.squareCharacterSection f f' s t w Q (C.sectionEquiv Q z)) D' =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f' Q (C'.sectionEquiv Q z') D' :=
    hs.symm.trans ((congrArg (fun y => y ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D' D s)
      (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply f D C Q z).symm).trans (hz.trans (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply f' D' C' Q z')))
  exact (D'.representable.homEquiv.apply_symm_apply _).symm.trans
    ((congrArg D'.representable.homEquiv hp).trans (D'.representable.homEquiv.apply_symm_apply _))

theorem cartierEvaluation_square (Q : Over (Spec (.of k)))
    (z : Q ⟶ C.dual.X) (z' : Q ⟶ C'.dual.X)
    (hz : (z ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C) ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D' D s = z' ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f' D' C')
    (x : Q ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f') :
    C'.evaluationValue Q z' x = C.evaluationValue Q z (x ≫ KernelCharacterSquares.kernelSquareMap f f' s t w) := by
  have h := congrArg
    (fun χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f'))).obj.obj (.op Q) =>
      CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ x) (cartierCharacter_square f f' s t w D D' C C' Q z z' hz).symm
  exact h.trans (ParameterCharacterSquares.squareCharacterSection_value f f' s t w Q (C.sectionEquiv Q z) x)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CartierEvaluationSquare
