import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.UnitBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseStructureSections

/-! # Unit Function Equiv -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.UnitFunctionEquiv.CechModelUnit

noncomputable section

/-! Degree-zero base-change cycles in a structure-sheaf Cech model are
the actual global functions on the pulled-back scheme, with its unit
cycle corresponding to the constant function one. -/

universe u
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

variable {X Y S T : Scheme.{u}} (a : Y ⟶ X) (f : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
  (h : a ≫ f = ρ ≫ g) {I : Type u} [LinearOrder I]
  (U : I → X.Opens) (hU : iSup U = ⊤)
  {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
  (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) U)
  [QuasiIsoAt (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap a f ρ g h (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) U φ) 0]

def baseChangeFunctionsEquiv :
    ((((ModuleCat.extendScalars g.appTop.hom).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj D).d 0 1).hom.ker ≃ₗ[Γ(T, ⊤)]
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y)).obj (op ⊤) :=
  (Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections a f ρ g h (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) U hU φ).trans
    (((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor ρ).mapIso (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso a)).app (op ⊤)).toLinearEquiv

theorem baseChangeFunctionsEquiv_apply
    (x : ((((ModuleCat.extendScalars g.appTop.hom).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj D).d 0 1).hom.ker) :
    baseChangeFunctionsEquiv a f ρ g h U hU φ x =
      (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso a).hom.app ⊤
        (Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections a f ρ g h (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) U hU φ x) := rfl

theorem baseChangeFunctionsEquiv_unit [QuasiIsoAt φ 0] :
    baseChangeFunctionsEquiv a f ρ g h U hU φ
      (Quotients.FiniteDescent.ModelOneTensor.Construction.CechBaseChangeMap.oneCycle g (ModelUnit.CechModelUnit.cycle f U hU φ)) = (1 : Γ(Y, ⊤)) := by
  rw [baseChangeFunctionsEquiv_apply, UnitBaseChange.CechModelUnit.baseChange_cycle_function]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.UnitFunctionEquiv.CechModelUnit
