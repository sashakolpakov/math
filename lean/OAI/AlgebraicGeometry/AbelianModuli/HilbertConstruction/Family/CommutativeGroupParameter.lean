import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.BaseChangeEquations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProperEquationParameters

/-! # Commutative Group Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.CommutativeGroupParameter

noncomputable section

/-! The closed group-law parameter carries actual universal commutative-group operations on the restricted proper-flat family. Its points classify precisely those base changes on which the prescribed operations are group operations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left]
variable {X : Over M.left} [IsProper X.hom] [Flat X.hom] (D : FamilyGroup.Operations.FamilyGroupOperations X)

def familyCommutativeGroupParameter : Over S := Finite.ProperEquationParameters.properEquationListParameter M D.equations

def familyCommutativeGroupParameterInclusion : familyCommutativeGroupParameter M D ⟶ M :=
  Finite.ProperEquationParameters.properEquationListParameterInclusion M D.equations

instance familyCommutativeGroupParameterInclusion_closed :
    IsClosedImmersion (familyCommutativeGroupParameterInclusion M D).left :=
  Finite.ProperEquationParameters.properEquationListParameterInclusion_closed M D.equations

def familyCommutativeGroupParameterPointEquiv (T : Over S) :
    (T ⟶ familyCommutativeGroupParameter M D) ≃
      {c : T ⟶ M // (D.baseChange c.left).Laws} :=
  (Finite.ProperEquationParameters.properEquationListParameterPointEquiv M D.equations T).trans
    { toFun := fun c => ⟨c.val, (D.baseChange_laws_iff c.val.left).mpr c.property⟩
      invFun := fun c => ⟨c.val, (D.baseChange_laws_iff c.val.left).mp c.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

def familyCommutativeGroupUniversalOperations :
    FamilyGroup.Operations.FamilyGroupOperations ((Over.pullback (familyCommutativeGroupParameterInclusion M D).left).obj X) :=
  D.baseChange (familyCommutativeGroupParameterInclusion M D).left

theorem familyCommutativeGroupUniversalOperations_laws :
    (familyCommutativeGroupUniversalOperations M D).Laws :=
  (D.baseChange_laws_iff (familyCommutativeGroupParameterInclusion M D).left).mpr
    (Finite.ProperEquationParameters.properEquationListParameter_universal M D.equations)

@[instance_reducible] def familyCommutativeGroupUniversalGroupObj :
    GrpObj ((Over.pullback (familyCommutativeGroupParameterInclusion M D).left).obj X) :=
  (familyCommutativeGroupUniversalOperations M D).groupObj
    (familyCommutativeGroupUniversalOperations_laws M D)

theorem familyCommutativeGroupUniversalGroupObj_comm :
    letI := familyCommutativeGroupUniversalGroupObj M D
    IsCommMonObj ((Over.pullback (familyCommutativeGroupParameterInclusion M D).left).obj X) :=
  (familyCommutativeGroupUniversalOperations M D).groupObj_comm
    (familyCommutativeGroupUniversalOperations_laws M D)

def familyCommutativeGroupParameterQuasiProjectivePresentation [IsNoetherian S]
    (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation M) : Projective.ProjectivePresentations.QuasiProjectivePresentation (familyCommutativeGroupParameter M D) :=
  Finite.ProperEquationParameters.properEquationListParameterQuasiProjectivePresentation M D.equations Q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.CommutativeGroupParameter
