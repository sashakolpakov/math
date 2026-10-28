import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProperEquationIdeals
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.IdealParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveParameterCuts

/-! # Proper Equation Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProperEquationParameters

noncomputable section

/-! A finite list of universal proper-flat morphism equations is represented by a specified closed parameter scheme, preserving quasi-projectivity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left]
variable (R : List (ProperEquationIdeals.ProperFamilyMorphismEquation M.left))

def properEquationListParameter : Over S := Closed.IdealParameter.closedIdealParameter M (ProperEquationIdeals.properEquationListIdeal R)

def properEquationListParameterInclusion : properEquationListParameter M R ⟶ M :=
  Closed.IdealParameter.closedIdealParameterInclusion M (ProperEquationIdeals.properEquationListIdeal R)

instance properEquationListParameterInclusion_closed :
    IsClosedImmersion (properEquationListParameterInclusion M R).left :=
  Closed.IdealParameter.closedIdealParameterInclusion_closed M (ProperEquationIdeals.properEquationListIdeal R)

def properEquationListParameterPointEquiv (T : Over S) :
    (T ⟶ properEquationListParameter M R) ≃
      {c : T ⟶ M // ∀ e ∈ R, (Over.pullback c.left).map e.lhs = (Over.pullback c.left).map e.rhs} :=
  (Closed.IdealParameter.closedIdealParameterPointEquiv M (ProperEquationIdeals.properEquationListIdeal R) T).trans
    { toFun := fun c => ⟨c.val, (ProperEquationIdeals.properEquationListIdeal_test R c.val.left).mp c.property⟩
      invFun := fun c => ⟨c.val, (ProperEquationIdeals.properEquationListIdeal_test R c.val.left).mpr c.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

theorem properEquationListParameter_universal :
    ∀ e ∈ R,
      (Over.pullback (properEquationListParameterInclusion M R).left).map e.lhs =
        (Over.pullback (properEquationListParameterInclusion M R).left).map e.rhs := by
  apply (ProperEquationIdeals.properEquationListIdeal_test R (properEquationListParameterInclusion M R).left).mp
  change (ProperEquationIdeals.properEquationListIdeal R).comap (ProperEquationIdeals.properEquationListIdeal R).subschemeι = ⊥
  rw [Closed.ConditionIdeals.ideal_comap_eq_bot_iff, Scheme.IdealSheafData.ker_subschemeι]

def properEquationListParameterQuasiProjectivePresentation [IsNoetherian S]
    (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation M) : Projective.ProjectivePresentations.QuasiProjectivePresentation (properEquationListParameter M R) :=
  Q.ofClosedImmersion (properEquationListParameterInclusion M R)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProperEquationParameters
