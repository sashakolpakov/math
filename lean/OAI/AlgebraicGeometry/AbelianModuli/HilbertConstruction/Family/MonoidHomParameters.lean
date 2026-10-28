import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MonoidHomEquations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProperEquationParameters

/-! # Monoid Hom Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MonoidHomParameters

noncomputable section

/-! The locus where a prescribed family morphism preserves multiplication and identity is a concrete closed parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left]
variable {X Y : Over M.left} [IsProper X.hom] [Flat X.hom] [IsSeparated Y.hom]
variable [MonObj X] [MonObj Y] (f : X ⟶ Y)

def familyMonoidHomParameter : Over S := Finite.ProperEquationParameters.properEquationListParameter M (MonoidHomEquations.familyMonoidHomEquations f)

def familyMonoidHomParameterInclusion : familyMonoidHomParameter M f ⟶ M :=
  Finite.ProperEquationParameters.properEquationListParameterInclusion M (MonoidHomEquations.familyMonoidHomEquations f)

instance familyMonoidHomParameterInclusion_closed :
    IsClosedImmersion (familyMonoidHomParameterInclusion M f).left :=
  Finite.ProperEquationParameters.properEquationListParameterInclusion_closed M (MonoidHomEquations.familyMonoidHomEquations f)

def familyMonoidHomParameterPointEquiv (T : Over S) :
    (T ⟶ familyMonoidHomParameter M f) ≃ {c : T ⟶ M // IsMonHom ((Over.pullback c.left).map f)} :=
  (Finite.ProperEquationParameters.properEquationListParameterPointEquiv M (MonoidHomEquations.familyMonoidHomEquations f) T).trans
    { toFun := fun c => ⟨c.val, (MonoidHomEquations.familyMonoidHomEquations_baseChange_iff f c.val.left).mpr c.property⟩
      invFun := fun c => ⟨c.val, (MonoidHomEquations.familyMonoidHomEquations_baseChange_iff f c.val.left).mp c.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

theorem familyMonoidHomParameter_universal :
    IsMonHom ((Over.pullback (familyMonoidHomParameterInclusion M f).left).map f) :=
  (MonoidHomEquations.familyMonoidHomEquations_baseChange_iff f (familyMonoidHomParameterInclusion M f).left).mpr
    (Finite.ProperEquationParameters.properEquationListParameter_universal M (MonoidHomEquations.familyMonoidHomEquations f))

def familyMonoidHomParameterQuasiProjectivePresentation [IsNoetherian S]
    (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation M) : Projective.ProjectivePresentations.QuasiProjectivePresentation (familyMonoidHomParameter M f) :=
  Finite.ProperEquationParameters.properEquationListParameterQuasiProjectivePresentation M (MonoidHomEquations.familyMonoidHomEquations f) Q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MonoidHomParameters
