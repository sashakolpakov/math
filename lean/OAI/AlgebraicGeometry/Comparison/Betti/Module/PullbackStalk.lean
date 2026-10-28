import OAI.AlgebraicGeometry.Comparison.Betti.PointModulePushforward
import OAI.AlgebraicGeometry.Comparison.Betti.StalkPointModuleAdjunction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-! # Pullback Stalk -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.PullbackStalk.Local

noncomputable section

/-! Stalks of the original sheaf-module pullback are extension of
scalars along the actual native structure-stalk map. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped IsMulCommutative

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}
  {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{0}}
  [(Opens.map f).IsContinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)]
  (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R) (x : X)
  [IsMulCommutative (TopCat.Presheaf.stalk (C := RingCat) (X := X) R.obj x)]
  [IsMulCommutative (TopCat.Presheaf.stalk (C := RingCat) (X := Y) S.obj (f x))]
  [(SheafOfModules.pushforward.{0} φ).IsRightAdjoint]

def modulePullbackStalkAdjunction :
    (SheafOfModules.pullback φ ⋙ StalkPointModuleAdjunction.Local.sheafRingModuleStalk R x) ⊣
      (PointModuleFunctor.Local.pointModuleSheafFunctor R x ⋙ SheafOfModules.pushforward φ) :=
  (SheafOfModules.pullbackPushforwardAdjunction φ).comp
    (StalkPointModuleAdjunction.Local.stalkPointModuleSheafAdjunction R x)

def moduleStalkExtensionAdjunction :
    (StalkPointModuleAdjunction.Local.sheafRingModuleStalk S (f x) ⋙ ModuleCat.extendScalars (RingedStalkPushforward.Local.ringedStalkMap f (R := R.obj) (S := S.obj) φ.hom x)) ⊣
      (ModuleCat.restrictScalars (RingedStalkPushforward.Local.ringedStalkMap f (R := R.obj) (S := S.obj) φ.hom x) ⋙ PointModuleFunctor.Local.pointModuleSheafFunctor S (f x)) :=
  (StalkPointModuleAdjunction.Local.stalkPointModuleSheafAdjunction S (f x)).comp
    (ModuleCat.extendRestrictScalarsAdj (RingedStalkPushforward.Local.ringedStalkMap f (R := R.obj) (S := S.obj) φ.hom x))

def modulePullbackStalkIso :
    SheafOfModules.pullback φ ⋙ StalkPointModuleAdjunction.Local.sheafRingModuleStalk R x ≅
      StalkPointModuleAdjunction.Local.sheafRingModuleStalk S (f x) ⋙ ModuleCat.extendScalars (RingedStalkPushforward.Local.ringedStalkMap f (R := R.obj) (S := S.obj) φ.hom x) :=
  Adjunction.leftAdjointUniq
    ((modulePullbackStalkAdjunction f φ x).ofNatIsoRight (PointModulePushforward.Local.pointModuleSheafPushforward f φ x))
    (moduleStalkExtensionAdjunction f φ x)

def moduleStalkIsoOfAdjunction {L : SheafOfModules.{0} S ⥤ SheafOfModules.{0} R}
    (adj : L ⊣ SheafOfModules.pushforward φ) :
    L ⋙ StalkPointModuleAdjunction.Local.sheafRingModuleStalk R x ≅
      StalkPointModuleAdjunction.Local.sheafRingModuleStalk S (f x) ⋙
        ModuleCat.extendScalars (RingedStalkPushforward.Local.ringedStalkMap f (R := R.obj) (S := S.obj) φ.hom x) :=
  Adjunction.leftAdjointUniq
    ((adj.comp (StalkPointModuleAdjunction.Local.stalkPointModuleSheafAdjunction R x)).ofNatIsoRight
      (PointModulePushforward.Local.pointModuleSheafPushforward f φ x))
    (moduleStalkExtensionAdjunction f φ x)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.PullbackStalk.Local
