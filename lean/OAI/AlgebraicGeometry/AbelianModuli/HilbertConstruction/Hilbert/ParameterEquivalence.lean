import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ParameterScheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmptyPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.UniversalBaseChange

/-! # Parameter Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ParameterEquivalence

noncomputable section

/-! The specified Hilbert parameter scheme classifies actual embedded Hilbert families on locally noetherian tests over any base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {T : Over S} [IsLocallyNoetherian T.left] (n : ℕ) (P : Polynomial ℚ)

def hilbertParameterEquiv : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P ≃ (T ⟶ ParameterScheme.hilbertParameterScheme S n P) := by
  classical
  unfold ParameterScheme.hilbertParameterScheme
  split_ifs with h
  · exact Relative.ParameterEquivalence.relativeProjectiveHilbertParameterEquiv le_rfl
      (ParameterScheme.hilbertParameterTruncation_flat n P) (ParameterScheme.hilbertParameterTruncation_test n P) h
  · exact EmptyPoints.relativeHilbertEmptyParameterEquiv le_rfl h

omit [IsLocallyNoetherian T.left] in
theorem hilbertParameterEquiv_inverse_of_eq {M M' : Over S} (hM : M = M')
    (e : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P ≃ (T ⟶ M'))
    (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily M'.left n P)
    (he : ∀ g : T ⟶ M', e.symm g = F.pullback g.left) :
    ∀ g : T ⟶ M,
      (Eq.mpr (congrArg (fun Z => RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P ≃ (T ⟶ Z)) hM) e).symm g =
        (Eq.mpr (congrArg (fun Z : Over S => RelativeProjective.Families.RelativeProjectiveHilbertFamily Z.left n P) hM) F).pullback g.left := by
  subst M'
  exact he

theorem hilbertParameterEquiv_inverse (g : T ⟶ ParameterScheme.hilbertParameterScheme S n P) :
    (hilbertParameterEquiv n P).symm g = (ParameterScheme.hilbertUniversalFamily S n P).pullback g.left := by
  classical
  revert g
  unfold hilbertParameterEquiv ParameterScheme.hilbertUniversalFamily ParameterScheme.hilbertParameterScheme
  split_ifs with h
  · apply hilbertParameterEquiv_inverse_of_eq n P (ite_eq_left h)
    intro g
    change Generated.ParameterFamilies.generatedParameterHilbertFamily g.left (ParameterScheme.hilbertParameterTruncation_flat n P)
        (ParameterScheme.hilbertParameterTruncation_test n P) h =
      (Generated.ParameterFamilies.generatedParameterHilbertFamily (𝟙 _) (ParameterScheme.hilbertParameterTruncation_flat n P)
        (ParameterScheme.hilbertParameterTruncation_test n P) h).pullback g.left
    simpa only [Category.comp_id] using
      (UniversalBaseChange.generatedParameterHilbertFamily_comp (ParameterScheme.hilbertParameterTruncation_flat n P)
        (ParameterScheme.hilbertParameterTruncation_test n P) h (𝟙 _) g.left).symm
  · apply hilbertParameterEquiv_inverse_of_eq n P (ite_eq_right h)
    intro g
    have : IsEmpty T.left := g.left.base.hom.1.isEmpty
    exact Subsingleton.elim _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ParameterEquivalence
