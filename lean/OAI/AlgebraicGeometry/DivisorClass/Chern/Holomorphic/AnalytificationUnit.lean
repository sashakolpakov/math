import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ModuleAnalytification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Limits.IsConnected

/-! # Analytification Unit -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AnalytificationUnit

noncomputable section

/-! The actual module analytification preserves the structure module and finite free modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

instance holomorphicAnalytificationSite_final :
    (Opens.map (RegularEvaluation.holomorphicAnalytificationPointMap V)).Final where
  out U := by
    let T : StructuredArrow U (Opens.map (RegularEvaluation.holomorphicAnalytificationPointMap V)) :=
      StructuredArrow.mk (Y := (⊤ : Opens V.carrier)) (homOfLE le_top)
    have hT : Limits.IsTerminal T := Limits.IsTerminal.ofUniqueHom
      (fun W => StructuredArrow.homMk (show W.right ⟶ (⊤ : Opens V.carrier) from homOfLE le_top))
      (fun _ _ => StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _))
    exact CategoryTheory.isConnected_of_isTerminal _ hT

def holomorphicAnalytificationUnitIso :
    (ModuleAnalytification.algebraicModuleHolomorphicAnalytification V).obj (SheafOfModules.unit V.carrier.ringCatSheaf) ≅
      SheafOfModules.unit (HolomorphicSection.Modules.holomorphicStructureRingSheaf V.analyticModel V.analyticSpace) :=
  asIso (SheafOfModules.pullbackObjUnitToUnit
    (F := Opens.map (RegularEvaluation.holomorphicAnalytificationPointMap V)) (RegularEvaluation.algebraicToHolomorphicStructureSheaf V))

def holomorphicAnalytificationFreeIso (I : Type) :
    (ModuleAnalytification.algebraicModuleHolomorphicAnalytification V).obj (SheafOfModules.free (R := V.carrier.ringCatSheaf) I) ≅
      SheafOfModules.free (R := HolomorphicSection.Modules.holomorphicStructureRingSheaf V.analyticModel V.analyticSpace) I :=
  SheafOfModules.pullbackObjFreeIso
    (F := Opens.map (RegularEvaluation.holomorphicAnalytificationPointMap V)) (RegularEvaluation.algebraicToHolomorphicStructureSheaf V) I

theorem holomorphicAnalytificationUnitIso_normalization :
    ((ModuleAnalytification.holomorphicModuleAnalytificationAdjunction V).homEquiv _ _)
      (holomorphicAnalytificationUnitIso V).hom =
        SheafOfModules.unitToPushforwardObjUnit
          (F := Opens.map (RegularEvaluation.holomorphicAnalytificationPointMap V)) (RegularEvaluation.algebraicToHolomorphicStructureSheaf V) :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AnalytificationUnit
