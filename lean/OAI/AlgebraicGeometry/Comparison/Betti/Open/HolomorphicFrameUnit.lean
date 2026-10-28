import OAI.AlgebraicGeometry.Comparison.Betti.Open.PullbackFrameUnit
import OAI.AlgebraicGeometry.Comparison.Betti.Open.PullbackNormalization

/-! # Holomorphic Frame Unit -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Comparison.Betti.Open.HolomorphicFrameUnit.RingedModules

/-! In the actual pulled-back open frame, the original adjunction unit sends
a regular module section to its original scalar evaluation in that frame. -/

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

theorem modulePullbackOverUnitIso_section_unit (M : SheafOfModules.{0} S)
    (e : M.over U ≅ SheafOfModules.unit (S.over U)) (m : M.val.obj (op U)) :
    (Analytification.OpenTrivialization.RingedModules.modulePullbackOverUnitIso φ U M e).hom.val.app (op (Over.mk (𝟙 (F.obj U))))
        (((SheafOfModules.pullbackPushforwardAdjunction φ).unit.app M).val.app (op U) m) =
      φ.hom.app (op U) (e.hom.val.app (op (Over.mk (𝟙 U))) m) := by
  let L := SheafOfModules.pullback φ
  let g := Analytification.OpenTrivialization.RingedModules.modulePullbackOverUnitIso φ U M e
  let t : (L.obj M).val.obj (op (F.obj U)) :=
    ((SheafOfModules.pullbackPushforwardAdjunction φ).unit.app M).val.app (op U) m
  let b : R.obj.obj (op (F.obj U ⨯ F.obj U)) :=
    g.hom.val.app (op ((Over.star (F.obj U)).obj (F.obj U)))
      ((L.obj M).val.map (prod.snd : F.obj U ⨯ F.obj U ⟶ F.obj U).op t)
  let c : S.obj.obj (op (U ⨯ U)) :=
    e.hom.val.app (op ((Over.star U).obj U)) (M.val.map (prod.snd : U ⨯ U ⟶ U).op m)
  have hu : R.obj.map (prodComparison F U U).op b = φ.hom.app (op (U ⨯ U)) c :=
    PullbackFrameUnit.RingedModules.modulePullbackOverUnitIso_product_unit φ U M e U m
  have hmap : R.obj.map (F.map (prod.lift (𝟙 U) (𝟙 U))).op
      (R.obj.map (prodComparison F U U).op b) =
      R.obj.map (prod.lift (𝟙 (F.obj U)) (𝟙 (F.obj U))).op b := by
    rw [← R.obj.map_comp_apply, ← op_comp, PullbackNormalization.RingedModules.prodComparison_map_diagonal]
  have hnat := ConcreteCategory.congr_hom (φ.hom.naturality (prod.lift (𝟙 U) (𝟙 U)).op) c
  exact (PullbackNormalization.RingedModules.openFrame_diagonal R (F.obj U) (L.obj M) g t).symm.trans
    (hmap.symm.trans ((congrArg (fun a : R.obj.obj (op (F.obj (U ⨯ U))) =>
      R.obj.map (F.map (prod.lift (𝟙 U) (𝟙 U))).op a) hu).trans
        (hnat.symm.trans (congrArg (fun a : S.obj.obj (op U) => φ.hom.app (op U) a)
          (PullbackNormalization.RingedModules.openFrame_diagonal S U M e m)))))

theorem modulePullbackOverUnitIso_generator (M : SheafOfModules.{0} S)
    (e : M.over U ≅ SheafOfModules.unit (S.over U)) :
    (Analytification.OpenTrivialization.RingedModules.modulePullbackOverUnitIso φ U M e).inv.val.app (op (Over.mk (𝟙 (F.obj U))))
        (1 : R.obj.obj (op (F.obj U))) =
      ((SheafOfModules.pullbackPushforwardAdjunction φ).unit.app M).val.app (op U)
        (e.inv.val.app (op (Over.mk (𝟙 U))) (1 : S.obj.obj (op U))) := by
  let A := (SheafOfModules.evaluation (R := R.over (F.obj U))
    (op (Over.mk (𝟙 (F.obj U))))).mapIso (Analytification.OpenTrivialization.RingedModules.modulePullbackOverUnitIso φ U M e)
  let B := (SheafOfModules.evaluation (R := S.over U) (op (Over.mk (𝟙 U)))).mapIso e
  let x : ((SheafOfModules.pullback φ).obj M).val.obj (op (F.obj U)) :=
    ((SheafOfModules.pullbackPushforwardAdjunction φ).unit.app M).val.app (op U)
      (e.inv.val.app (op (Over.mk (𝟙 U))) (1 : S.obj.obj (op U)))
  have h := modulePullbackOverUnitIso_section_unit φ U M e
    (e.inv.val.app (op (Over.mk (𝟙 U))) (1 : S.obj.obj (op U)))
  have hx : A.hom x = (1 : R.obj.obj (op (F.obj U))) :=
    h.trans ((congrArg (fun r : S.obj.obj (op U) => φ.hom.app (op U) r)
      (Iso.inv_hom_id_apply B (1 : S.obj.obj (op U)))).trans (φ.hom.app (op U)).hom.map_one)
  exact (congrArg (fun r : R.obj.obj (op (F.obj U)) => A.inv r) hx).symm.trans
    (Iso.hom_inv_id_apply A x)

end AlgebraicGeometry.Comparison.Betti.Open.HolomorphicFrameUnit.RingedModules

namespace AlgebraicGeometry.Comparison.Betti.Open.HolomorphicFrameUnit

/-! The original analytification unit is normalized in every actual open line
frame. In particular, it sends the algebraic frame generator to the analytic
frame generator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem holomorphicAnalytificationOpenUnitIso_section_unit (U : X.left.Opens)
    (M : SheafOfModules.{0} X.left.ringCatSheaf)
    (e : M.over U ≅ SheafOfModules.unit (X.left.ringCatSheaf.over U))
    (m : M.val.obj (op U)) :
    (Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso X U M e).hom.val.app (op (Over.mk (𝟙 (AffineIsoEvaluation.analyticOpen X U))))
        (((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X).unit.app M).val.app (op U) m) =
      Holomorphic.RegularSections.regularHolomorphicSectionMap X U (e.hom.val.app (op (Over.mk (𝟙 U))) m) := by
  exact @RingedModules.modulePullbackOverUnitIso_section_unit
    (Opens X.left) (Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) inferInstance inferInstance
    inferInstance inferInstance (Opens.grothendieckTopology X.left)
    (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Opens.map (Analytification.Base.analytificationMap X))
    (Holomorphic.StructureMorphism.holomorphicAnalytificationSite_continuous X) X.left.ringCatSheaf
    (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X) (Holomorphic.StructureMorphism.algebraicToHolomorphicStructureSheaf X) U
    (Holomorphic.AnalytificationOpenFrames.holomorphicOverSite_continuous X U)
    (fun V => OpensInverseImageLimits.RingedModules.opensMap_prodComparison_isIso (Analytification.Base.analytificationMap X) U V)
    (Holomorphic.StructureMorphism.holomorphicModuleDirectImage_isRightAdjoint X)
    (Holomorphic.AnalytificationOpenFrames.holomorphicOverModulePushforward_isRightAdjoint X U) M e m

theorem holomorphicAnalytificationOpenUnitIso_generator (U : X.left.Opens)
    (M : SheafOfModules.{0} X.left.ringCatSheaf)
    (e : M.over U ≅ SheafOfModules.unit (X.left.ringCatSheaf.over U)) :
    (Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso X U M e).inv.val.app (op (Over.mk (𝟙 (AffineIsoEvaluation.analyticOpen X U))))
        (1 : (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X).obj.obj (op (AffineIsoEvaluation.analyticOpen X U))) =
      ((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X).unit.app M).val.app (op U)
        (e.inv.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X.left, U))) := by
  exact @RingedModules.modulePullbackOverUnitIso_generator
    (Opens X.left) (Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) inferInstance inferInstance
    inferInstance inferInstance (Opens.grothendieckTopology X.left)
    (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Opens.map (Analytification.Base.analytificationMap X))
    (Holomorphic.StructureMorphism.holomorphicAnalytificationSite_continuous X) X.left.ringCatSheaf
    (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X) (Holomorphic.StructureMorphism.algebraicToHolomorphicStructureSheaf X) U
    (Holomorphic.AnalytificationOpenFrames.holomorphicOverSite_continuous X U)
    (fun V => OpensInverseImageLimits.RingedModules.opensMap_prodComparison_isIso (Analytification.Base.analytificationMap X) U V)
    (Holomorphic.StructureMorphism.holomorphicModuleDirectImage_isRightAdjoint X)
    (Holomorphic.AnalytificationOpenFrames.holomorphicOverModulePushforward_isRightAdjoint X U) M e

end AlgebraicGeometry.Comparison.Betti.Open.HolomorphicFrameUnit

end

end OAI
