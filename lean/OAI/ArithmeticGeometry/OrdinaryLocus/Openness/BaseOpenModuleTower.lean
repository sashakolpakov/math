import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections

/-! # Base Open Module Tower -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction

noncomputable section

/-! The two scalar actions on local module sections form the actual base-to-open scalar tower. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

@[instance_reducible]
def baseOpenModuleOverSections {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (U : X.Opens) :
    Module Γ(X, U) ((BaseOpenSections.Construction.baseOpenSectionsFunctor π U).obj M) := inferInstanceAs (Module Γ(X, U) Γ(M, U))

theorem baseOpenModuleScalarTower {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (U : X.Opens) :
    letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra π U
    letI := baseOpenModuleOverSections π M U
    IsScalarTower Γ(S, ⊤) Γ(X, U) ((BaseOpenSections.Construction.baseOpenSectionsFunctor π U).obj M) :=
  letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra π U
  letI := baseOpenModuleOverSections π M U
  { smul_assoc := fun r a x => mul_smul (BaseOpenSections.Construction.baseOpenScalarMap π U r) a x }

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction
