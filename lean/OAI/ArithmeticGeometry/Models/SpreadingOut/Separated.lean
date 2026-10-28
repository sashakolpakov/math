import OAI.ArithmeticGeometry.Models.SpreadingOut.SeparatedDescent
import OAI.ArithmeticGeometry.Models.General

/-! # Separated -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.Separated.Construction

noncomputable section

/-! Actual separated coefficient models of separated finite-presentation schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

open OAI.ArithmeticGeometry.Models.General.Constructions.Foundations

theorem separated_scheme_has_coefficient_model
    {K : Type u} [Field K] [NumberField K]
    (X : Over (Spec (CommRingCat.of K))) [IsSeparated X.hom]
    (hX : Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) :
    ∃ M : Foundations.Constructions.CoefficientModel K X, IsSeparated M.model.hom := by
  obtain ⟨M⟩ := General.Constructions.Foundations.scheme_has_coefficient_model X hX
  have : IsIso M.genericIso.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map M.genericIso.hom))
  have hs : IsSeparated (M.genericIso.hom.left ≫ X.hom) := inferInstance
  rw [M.genericIso.hom.w] at hs
  have := hs
  obtain ⟨t, h, ht⟩ := SeparatedDescent.Construction.separated_generic_model_eventually_separated M.model
    M.finitePresentation
  exact ⟨M.enlarge t h, ht⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.Separated.Construction
