import OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteFlatChartModule
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower

/-! # Factored Pushforward Open Module -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FactoredPushforwardOpenModule.Dimension

noncomputable section

/-! Local sections of a composite pushforward carry the intermediate affine ring's module action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction

universe u

@[instance_reducible]
def factoredPushforwardOpenModule {X Z Y S : Scheme.{u}}
    (f : X ⟶ Z) (a : Z ⟶ Y) (π : Y ⟶ S) (U : Y.Opens) :
    Module Γ(Z, a ⁻¹ᵁ U) ((ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsFunctor π U).obj
      ((Scheme.Modules.pushforward (f ≫ a)).obj (Invertible.Scheme.Modules.unitObj X))) :=
  let := FiniteFlatChartModule.Dimension.affinePreimageSectionAlgebra f (a ⁻¹ᵁ U)
  inferInstanceAs (Module Γ(Z, a ⁻¹ᵁ U) Γ(X, f ⁻¹ᵁ (a ⁻¹ᵁ U)))

theorem factoredPushforwardOpenModule_smul {X Z Y S : Scheme.{u}}
    (f : X ⟶ Z) (a : Z ⟶ Y) (π : Y ⟶ S) (U : Y.Opens) :
    let N := (Scheme.Modules.pushforward (f ≫ a)).obj (Invertible.Scheme.Modules.unitObj X)
    letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction.baseOpenModuleOverSections π N U
    letI := factoredPushforwardOpenModule f a π U
    ∀ (r : Γ(Y, U)) (x : (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsFunctor π U).obj N),
      r • x = a.app U r • x := by
  intro N
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction.baseOpenModuleOverSections π N U
  let := factoredPushforwardOpenModule f a π U
  intro r x
  change Γ(X, f ⁻¹ᵁ (a ⁻¹ᵁ U)) at x
  rfl

theorem factoredPushforwardOpenModule_tower {X Z Y S : Scheme.{u}}
    (f : X ⟶ Z) (a : Z ⟶ Y) (π : Y ⟶ S) (U : Y.Opens) :
    letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (a ≫ π) (a ⁻¹ᵁ U)
    letI := factoredPushforwardOpenModule f a π U
    IsScalarTower Γ(S, ⊤) Γ(Z, a ⁻¹ᵁ U) ((ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsFunctor π U).obj
      ((Scheme.Modules.pushforward (f ≫ a)).obj (Invertible.Scheme.Modules.unitObj X))) := by
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (a ≫ π) (a ⁻¹ᵁ U)
  let := factoredPushforwardOpenModule f a π U
  constructor
  intro r b x
  change Γ(X, f ⁻¹ᵁ (a ⁻¹ᵁ U)) at x
  change f.app (a ⁻¹ᵁ U) (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenScalarMap (a ≫ π) (a ⁻¹ᵁ U) r * b) * x =
    f.app (a ⁻¹ᵁ U) (a.app U (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenScalarMap π U r)) * (f.app (a ⁻¹ᵁ U) b * x)
  rw [map_mul, mul_assoc]
  rw [← RingHom.congr_fun (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenScalarMap_pullback a π U) r]
  rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FactoredPushforwardOpenModule.Dimension
