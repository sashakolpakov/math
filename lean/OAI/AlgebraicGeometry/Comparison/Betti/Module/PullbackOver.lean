import OAI.AlgebraicGeometry.Comparison.Betti.OverRingedComposition
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-! # Pullback Over -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.PullbackOver.RingedModules

noncomputable section

/-! Actual module pullback commutes with open-slice restriction by the normalized pushforward square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D : Type} [SmallCategory C] [SmallCategory D]
  [HasBinaryProducts C] [HasBinaryProducts D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  {S : Sheaf J RingCat.{0}} {R : Sheaf K RingCat.{0}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R) (U : C)
  [(Over.post (X := U) F).IsContinuous (J.over U) (K.over (F.obj U))]
  [∀ V, IsIso (prodComparison F U V)]

attribute [local instance] OverRingedComposition.Modules.starPost_continuous OverRingedComposition.Modules.postStar_continuous

def overPushforwardSquareIso :
    SheafOfModules.pushforward.{0} (SheafOfModules.pushforwardOver (R := R) (F.obj U)) ⋙
        SheafOfModules.pushforward φ ≅
      SheafOfModules.pushforward.{0} (OverRingedMorphism.Modules.overStructureMap φ U) ⋙
        SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := S) U) :=
  SheafOfModules.pushforwardComp φ (SheafOfModules.pushforwardOver (R := R) (F.obj U)) ≪≫
    SheafOfModules.pushforwardCongr₂ (φ := OverRingedComposition.Modules.overSecondCompositeStructure φ U)
      (OverProduct.RingedModules.overStarPostIso F U) (OverRingedComposition.Modules.overCompositeStructure_normalization φ U) ≪≫
        (SheafOfModules.pushforwardComp (SheafOfModules.pushforwardOver (R := S) U)
          (OverRingedMorphism.Modules.overStructureMap φ U)).symm

variable [(SheafOfModules.pushforward.{0} φ).IsRightAdjoint]
  [(SheafOfModules.pushforward.{0} (OverRingedMorphism.Modules.overStructureMap φ U)).IsRightAdjoint]

def modulePullbackOverIso :
    SheafOfModules.pullback.{0} φ ⋙ SheafOfModules.overFunctor R (F.obj U) ≅
      SheafOfModules.overFunctor S U ⋙ SheafOfModules.pullback.{0} (OverRingedMorphism.Modules.overStructureMap φ U) :=
  Adjunction.leftAdjointUniq
    (((SheafOfModules.pullbackPushforwardAdjunction φ).comp
      (SheafOfModules.overPushforwardOverAdj (R := R) (F.obj U))).ofNatIsoRight
        (overPushforwardSquareIso φ U))
    ((SheafOfModules.overPushforwardOverAdj (R := S) U).comp
      (SheafOfModules.pullbackPushforwardAdjunction (OverRingedMorphism.Modules.overStructureMap φ U)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.PullbackOver.RingedModules
