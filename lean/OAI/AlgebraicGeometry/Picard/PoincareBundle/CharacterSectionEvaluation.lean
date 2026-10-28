import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Evaluation

/-! # Character Section Evaluation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterSectionEvaluation

noncomputable section

/-! Evaluation of represented characters after arbitrary parameter restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Evaluation.Construction

/-- A restricted representing point evaluates by the original character's component on that test scheme. -/
theorem value {S : Scheme.{u}} {G : Grp (Over S)} (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G)
    {Q T : Over S} (a : T ⟶ Q) (d : Q ⟶ C.dual.X) (x : T ⟶ G.X) :
    C.evaluationValue T (a ≫ d) x = (C.sectionEquiv Q d).app (.op (Over.mk a)) x :=
  (congrArg (fun χ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (.op T) => AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ x)
    (C.sectionEquiv_natural a d)).trans (AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value_restrict a (C.sectionEquiv Q d) x)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterSectionEvaluation
