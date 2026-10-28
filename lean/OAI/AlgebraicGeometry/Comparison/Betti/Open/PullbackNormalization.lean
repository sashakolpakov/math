import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.OpenTrivialization
import OAI.AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness

/-! # Pullback Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.PullbackNormalization.RingedModules

noncomputable section

section

/-! Normalization of the actual pullback open frame under its defining
adjunctions. The scalar map is the original unit-to-pushforward map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

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

theorem modulePullbackOverUnitIso_homEquiv (M : SheafOfModules.{0} S)
    (e : M.over U ≅ SheafOfModules.unit (S.over U)) :
    (SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv M _
        ((SheafOfModules.overPushforwardOverAdj (R := R) (F.obj U)).homEquiv
          ((SheafOfModules.pullback φ).obj M) _ (Analytification.OpenTrivialization.RingedModules.modulePullbackOverUnitIso φ U M e).hom) ≫
        (Module.PullbackOver.RingedModules.overPushforwardSquareIso φ U).hom.app (SheafOfModules.unit (R.over (F.obj U))) =
      (SheafOfModules.overPushforwardOverAdj (R := S) U).homEquiv M _
        (e.hom ≫ SheafOfModules.unitToPushforwardObjUnit (OverRingedMorphism.Modules.overStructureMap φ U)) := by
  have h := AdjunctionComplexUniqueness.leftAdjointUniq_homEquiv
    (((SheafOfModules.pullbackPushforwardAdjunction φ).comp
      (SheafOfModules.overPushforwardOverAdj (R := R) (F.obj U))).ofNatIsoRight
        (Module.PullbackOver.RingedModules.overPushforwardSquareIso φ U))
    ((SheafOfModules.overPushforwardOverAdj (R := S) U).comp
      (SheafOfModules.pullbackPushforwardAdjunction (OverRingedMorphism.Modules.overStructureMap φ U)))
    ((SheafOfModules.pullback (OverRingedMorphism.Modules.overStructureMap φ U)).map e.hom ≫
      SheafOfModules.pullbackObjUnitToUnit (OverRingedMorphism.Modules.overStructureMap φ U))
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv,
    Adjunction.comp_homEquiv] at h
  exact h.trans (congrArg ((SheafOfModules.overPushforwardOverAdj (R := S) U).homEquiv M _)
    (((SheafOfModules.pullbackPushforwardAdjunction (OverRingedMorphism.Modules.overStructureMap φ U)).homEquiv_naturality_left
      e.hom (SheafOfModules.pullbackObjUnitToUnit (OverRingedMorphism.Modules.overStructureMap φ U))).trans
        (congrArg (fun f => e.hom ≫ f)
          (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
            (OverRingedMorphism.Modules.overStructureMap φ U)))))

end

section

/-! Section formulas for the original open-slice adjunction and the normalized
pullback square. These expose the actual restriction maps in an open frame. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

section OpenAdjunction

variable {C : Type} [SmallCategory C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} (S : Sheaf J RingCat.{0}) (U : C)

theorem overModuleHomEquiv_apply (M : SheafOfModules.{0} S)
    (N : SheafOfModules.{0} (S.over U)) (g : M.over U ⟶ N)
    (V : Cᵒᵖ) (m : M.val.obj V) :
    (((SheafOfModules.overPushforwardOverAdj (R := S) U).homEquiv M N g).val.app V) m =
      g.val.app (op ((Over.star U).obj V.unop)) (M.val.map prod.snd.op m) := by
  erw [Adjunction.homEquiv_apply]
  change g.val.app (op ((Over.star U).obj V.unop))
    (M.val.map ((Over.forgetAdjStar U).counit.app V.unop).op m) = _
  rw [Over.forgetAdjStar_counit_app]
  rfl

end OpenAdjunction

variable {C D : Type} [SmallCategory C] [SmallCategory D]
  [HasBinaryProducts C] [HasBinaryProducts D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  {S : Sheaf J RingCat.{0}} {R : Sheaf K RingCat.{0}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R) (U : C)
  [(Over.post (X := U) F).IsContinuous (J.over U) (K.over (F.obj U))]
  [∀ V, IsIso (prodComparison F U V)]

theorem overPushforwardSquareIso_apply (N : SheafOfModules.{0} (R.over (F.obj U)))
    (V : Cᵒᵖ)
    (a : ((SheafOfModules.pushforward.{0} φ).obj
      ((SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := R) (F.obj U))).obj N)).val.obj V) :
    ((Module.PullbackOver.RingedModules.overPushforwardSquareIso φ U).hom.app N).val.app V a =
      N.val.map ((OverProduct.RingedModules.overStarPostIso F U).hom.app V.unop).op a := rfl

end

/-! Restricting the product used by the over-site along its diagonal recovers
the original frame coordinate. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

variable {C D : Type} [SmallCategory C] [SmallCategory D]
  [HasBinaryProducts C] [HasBinaryProducts D]

theorem prodComparison_map_diagonal (F : C ⥤ D) (U : C) :
    F.map (prod.lift (𝟙 U) (𝟙 U)) ≫ prodComparison F U U =
      prod.lift (𝟙 (F.obj U)) (𝟙 (F.obj U)) := by
  apply prod.hom_ext
  · rw [Category.assoc, prodComparison_fst, ← F.map_comp, prod.lift_fst, F.map_id, prod.lift_fst]
  · rw [Category.assoc, prodComparison_snd, ← F.map_comp, prod.lift_snd, F.map_id, prod.lift_snd]

variable {J : GrothendieckTopology C} (S : Sheaf J RingCat.{0}) (U : C)

theorem moduleSection_diagonal (M : SheafOfModules.{0} S) (m : M.val.obj (op U)) :
    M.val.map (prod.lift (𝟙 U) (𝟙 U)).op
      (M.val.map (prod.snd : U ⨯ U ⟶ U).op m) = m := by
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, prod.lift_snd, op_id, M.val.map_id]
  rfl

theorem openFrame_diagonal (M : SheafOfModules.{0} S)
    (e : M.over U ≅ SheafOfModules.unit (S.over U)) (m : M.val.obj (op U)) :
    S.obj.map (prod.lift (𝟙 U) (𝟙 U)).op
        (e.hom.val.app (op ((Over.star U).obj U)) (M.val.map (prod.snd : U ⨯ U ⟶ U).op m)) =
      e.hom.val.app (op (Over.mk (𝟙 U))) m := by
  let f : Over.mk (𝟙 U) ⟶ (Over.star U).obj U :=
    Over.homMk (prod.lift (𝟙 U) (𝟙 U)) (by
      change prod.lift (𝟙 U) (𝟙 U) ≫ (prod.lift prod.fst (𝟙 (U ⨯ U)) ≫ prod.fst) = 𝟙 U
      rw [prod.lift_fst, prod.lift_fst])
  have h := PresheafOfModules.naturality_apply e.hom.val f.op
    (M.val.map (prod.snd : U ⨯ U ⟶ U).op m)
  exact h.symm.trans (congrArg (fun a => e.hom.val.app (op (Over.mk (𝟙 U))) a)
    (moduleSection_diagonal S U M m))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.PullbackNormalization.RingedModules
