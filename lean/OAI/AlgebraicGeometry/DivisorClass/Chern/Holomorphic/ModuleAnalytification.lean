import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RegularEvaluation
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-! # Module Analytification -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ModuleAnalytification

noncomputable section

/-! Analytification of actual algebraic module sheaves along regular-function evaluation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

def holomorphicModuleDirectImage :
    SheafOfModules (HolomorphicSection.Modules.holomorphicStructureRingSheaf V.analyticModel V.analyticSpace) ⥤ V.carrier.Modules :=
  SheafOfModules.pushforward (F := Opens.map (RegularEvaluation.holomorphicAnalytificationPointMap V))
    (RegularEvaluation.algebraicToHolomorphicStructureSheaf V)

def algebraicModuleHolomorphicAnalytification :
    V.carrier.Modules ⥤ SheafOfModules (HolomorphicSection.Modules.holomorphicStructureRingSheaf V.analyticModel V.analyticSpace) :=
  SheafOfModules.pullback (F := Opens.map (RegularEvaluation.holomorphicAnalytificationPointMap V))
    (RegularEvaluation.algebraicToHolomorphicStructureSheaf V)

def holomorphicModuleAnalytificationAdjunction :
    algebraicModuleHolomorphicAnalytification V ⊣ holomorphicModuleDirectImage V :=
  SheafOfModules.pullbackPushforwardAdjunction
    (F := Opens.map (RegularEvaluation.holomorphicAnalytificationPointMap V)) (RegularEvaluation.algebraicToHolomorphicStructureSheaf V)

instance algebraicModuleHolomorphicAnalytification_isLeftAdjoint :
    (algebraicModuleHolomorphicAnalytification V).IsLeftAdjoint :=
  (holomorphicModuleAnalytificationAdjunction V).isLeftAdjoint

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ModuleAnalytification
