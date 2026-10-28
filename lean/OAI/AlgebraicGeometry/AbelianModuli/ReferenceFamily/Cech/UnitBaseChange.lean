import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ModelUnit
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SectionBaseChange
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackModuleSections

/-! # Unit Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.UnitBaseChange.CechModelUnit

noncomputable section

/-! The unit cycle of a structure-sheaf Cech model remains the actual
constant function one on every base change computed by that model. -/

universe u
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackModuleSections.Construction

theorem pullbackTopSection_eq_global {X Y : Scheme.{u}} (a : Y ⟶ X)
    (M : X.Modules) (s : Γ(M, ⊤)) :
    PELModuli.IntegralModel.CechPullbackSectionNormalization.pullbackTopSection a M s = ArithmeticGeometry.OrdinaryLocus.Openness.PullbackModuleSections.Construction.modulePullbackGlobalSection a M s := by
  change ((Scheme.Modules.pullback a).obj M).presheaf.map (𝟙 (op (⊤ : Y.Opens)))
    (ArithmeticGeometry.OrdinaryLocus.Openness.PullbackModuleSections.Construction.modulePullbackGlobalSection a M s) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

variable {X Y S T : Scheme.{u}} (a : Y ⟶ X) (f : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
  (h : a ≫ f = ρ ≫ g) {I : Type u} [LinearOrder I]
  (U : I → X.Opens) (hU : iSup U = ⊤)
  {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
  (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) U)
  [QuasiIsoAt φ 0] [QuasiIsoAt (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap a f ρ g h (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) U φ) 0]

theorem baseChange_cycle_section :
    Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections a f ρ g h (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) U hU φ
      (Quotients.FiniteDescent.ModelOneTensor.Construction.CechBaseChangeMap.oneCycle g (ModelUnit.CechModelUnit.cycle f U hU φ)) =
        PELModuli.IntegralModel.CechPullbackSectionNormalization.pullbackTopSection a (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) (1 : Γ(X, ⊤)) := by
  rw [PELModuli.IntegralModel.SectionBaseChange.modelKernelSections_one a f ρ g h (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) U hU φ, ModelUnit.CechModelUnit.cycle_section]

theorem baseChange_cycle_function :
    (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso a).hom.app ⊤
      (Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections a f ρ g h (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) U hU φ
        (Quotients.FiniteDescent.ModelOneTensor.Construction.CechBaseChangeMap.oneCycle g (ModelUnit.CechModelUnit.cycle f U hU φ))) = (1 : Γ(Y, ⊤)) := by
  exact (congrArg ((ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso a).hom.app ⊤)
    ((baseChange_cycle_section a f ρ g h U hU φ).trans
      (pullbackTopSection_eq_global a (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) (1 : Γ(X, ⊤))))).trans
    ((ArithmeticGeometry.OrdinaryLocus.Openness.PullbackModuleSections.Construction.modulePullbackGlobalSection_unit a (1 : Γ(X, ⊤))).trans a.appTop.hom.map_one)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.UnitBaseChange.CechModelUnit
