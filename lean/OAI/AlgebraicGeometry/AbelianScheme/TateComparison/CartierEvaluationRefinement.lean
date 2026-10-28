import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CharacterCoverRefinement
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism

/-! # Cartier Evaluation Refinement -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CartierEvaluationRefinement

noncomputable section

/-! Equality of actual Picard points forces the expected restriction
identity on Cartier evaluation under a refinement of group covers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism.Construction.KernelCharacters

universe u
variable {k : Type u} [Field k] {A A' B : Over (Spec (.of k))}
  [GrpObj A] [GrpObj A'] [GrpObj B]
  [Smooth A'.hom] [IsProper A'.hom] [GeometricallyConnected A'.hom]
  (f : A ⟶ B) (f' : A' ⟶ B) [IsMonHom f] [IsMonHom f']
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  [IsAffineHom f'.left] [Flat f'.left] [Surjective f'.left] [LocallyOfFinitePresentation f'.left]
  (t : A' ⟶ A) [IsMonHom t] (w : t ≫ f = f') (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  (C' : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f')))

theorem cartierCharacter_refinement (Q : Over (Spec (.of k)))
    (z : Q ⟶ C.dual.X) (z' : Q ⟶ C'.dual.X)
    (hz : z ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C = z' ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f' D C') :
    CharacterCoverRefinement.refinementCharacterSection f f' t w Q (C.sectionEquiv Q z) = C'.sectionEquiv Q z' := by
  apply CartierDuality.PicardMonomorphism.Construction.KernelCharacters.parameterCharacterPicardHom_injective f' Q
  have h := CharacterCoverRefinement.parameterCharacterDualPoint_refinement f f' t w Q (C.sectionEquiv Q z) D
  have hp : CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f' Q (CharacterCoverRefinement.refinementCharacterSection f f' t w Q (C.sectionEquiv Q z)) D =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f' Q (C'.sectionEquiv Q z') D :=
    h.trans ((CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply f D C Q z).symm.trans
      (hz.trans (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply f' D C' Q z')))
  exact (D.representable.homEquiv.apply_symm_apply _).symm.trans
    ((congrArg D.representable.homEquiv hp).trans (D.representable.homEquiv.apply_symm_apply _))

theorem cartierEvaluation_refinement (Q : Over (Spec (.of k)))
    (z : Q ⟶ C.dual.X) (z' : Q ⟶ C'.dual.X)
    (hz : z ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C = z' ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f' D C')
    (x : Q ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f') :
    C'.evaluationValue Q z' x = C.evaluationValue Q z
      (x ≫ KernelCharacterSquares.kernelSquareMap f f' (𝟙 B) t (w.trans (Category.comp_id f').symm)) := by
  have h := congrArg
    (fun χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f'))).obj.obj (.op Q) =>
      CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ x) (cartierCharacter_refinement f f' t w D C C' Q z z' hz).symm
  exact h.trans (ParameterCharacterSquares.squareCharacterSection_value f f' (𝟙 B) t
    (w.trans (Category.comp_id f').symm) Q (C.sectionEquiv Q z) x)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CartierEvaluationRefinement
