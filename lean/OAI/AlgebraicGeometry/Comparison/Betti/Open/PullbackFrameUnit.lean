import OAI.AlgebraicGeometry.Comparison.Betti.Open.PullbackNormalization

/-! # Pullback Frame Unit -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.PullbackFrameUnit.RingedModules

noncomputable section

/-! The actual pulled-back open frame sends the original adjunction unit to
the original scalar evaluation, first on the product used by the over-site. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

variable {C D : Type} [SmallCategory C] [SmallCategory D]
  [HasBinaryProducts C] [HasBinaryProducts D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  {S : Sheaf J RingCat.{0}} {R : Sheaf K RingCat.{0}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R) (U : C)
  [(Over.post (X := U) F).IsContinuous (J.over U) (K.over (F.obj U))]
  [∀ V, IsIso (prodComparison F U V)]
  [(SheafOfModules.pushforward.{0} φ).IsRightAdjoint]
  [(SheafOfModules.pushforward.{0} (OverRingedMorphism.Modules.overStructureMap φ U)).IsRightAdjoint]

theorem modulePullbackOverUnitIso_product_unit (M : SheafOfModules.{0} S)
    (e : M.over U ≅ SheafOfModules.unit (S.over U)) (V : C) (m : M.val.obj (op V)) :
    R.obj.map (prodComparison F U V).op
        ((Analytification.OpenTrivialization.RingedModules.modulePullbackOverUnitIso φ U M e).hom.val.app (op ((Over.star (F.obj U)).obj (F.obj V)))
          (((SheafOfModules.pullback φ).obj M).val.map prod.snd.op
            (((SheafOfModules.pullbackPushforwardAdjunction φ).unit.app M).val.app (op V) m))) =
      φ.hom.app (op (U ⨯ V))
        (e.hom.val.app (op ((Over.star U).obj V)) (M.val.map prod.snd.op m)) := by
  have h := PullbackNormalization.RingedModules.modulePullbackOverUnitIso_homEquiv φ U M e
  rw [Adjunction.homEquiv_apply] at h
  have hm := congrArg (fun f => f.val.app (op V) m) h
  change ((Module.PullbackOver.RingedModules.overPushforwardSquareIso φ U).hom.app (SheafOfModules.unit (R.over (F.obj U)))).val.app (op V)
    ((((SheafOfModules.overPushforwardOverAdj (R := R) (F.obj U)).homEquiv
      ((SheafOfModules.pullback φ).obj M) _ (Analytification.OpenTrivialization.RingedModules.modulePullbackOverUnitIso φ U M e).hom).val.app (op (F.obj V)))
        (((SheafOfModules.pullbackPushforwardAdjunction φ).unit.app M).val.app (op V) m)) =
    (((SheafOfModules.overPushforwardOverAdj (R := S) U).homEquiv M _
      (e.hom ≫ SheafOfModules.unitToPushforwardObjUnit (OverRingedMorphism.Modules.overStructureMap φ U))).val.app (op V)) m at hm
  have hl := PullbackNormalization.RingedModules.overModuleHomEquiv_apply R (F.obj U) ((SheafOfModules.pullback φ).obj M)
    (SheafOfModules.unit (R.over (F.obj U))) (Analytification.OpenTrivialization.RingedModules.modulePullbackOverUnitIso φ U M e).hom (op (F.obj V))
      (((SheafOfModules.pullbackPushforwardAdjunction φ).unit.app M).val.app (op V) m)
  have hs := PullbackNormalization.RingedModules.overPushforwardSquareIso_apply φ U (SheafOfModules.unit (R.over (F.obj U))) (op V)
    ((((SheafOfModules.overPushforwardOverAdj (R := R) (F.obj U)).homEquiv
      ((SheafOfModules.pullback φ).obj M) _ (Analytification.OpenTrivialization.RingedModules.modulePullbackOverUnitIso φ U M e).hom).val.app (op (F.obj V)))
        (((SheafOfModules.pullbackPushforwardAdjunction φ).unit.app M).val.app (op V) m))
  have hr := PullbackNormalization.RingedModules.overModuleHomEquiv_apply S U M
    ((SheafOfModules.pushforward (OverRingedMorphism.Modules.overStructureMap φ U)).obj (SheafOfModules.unit (R.over (F.obj U))))
    (e.hom ≫ SheafOfModules.unitToPushforwardObjUnit (OverRingedMorphism.Modules.overStructureMap φ U)) (op V) m
  exact (congrArg (fun a : R.obj.obj (op (F.obj U ⨯ F.obj V)) =>
    R.obj.map (prodComparison F U V).op a) hl).symm.trans (hs.symm.trans (hm.trans hr))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.PullbackFrameUnit.RingedModules
