import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.PushforwardUnitGerms
import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.StalkUnitNormalization

/-! # Stalk -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytification.Stalk

noncomputable section

section

/-! The actual pushforward comparison in stalk tensor coordinates, normalized on every original algebraic stalk element. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

def moduleAnalytificationStalkComparison (M : X.left.Modules) :
    (ModuleCat.extendScalars (RingedStalk.analytificationRingedStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p))).obj
      ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of Y.left) Y.left.ringCatSheaf
        (Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p))).obj
          ((Scheme.Modules.pushforward f.left).obj M)) ⟶
    (ModuleCat.restrictScalars (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback f p)).obj
      ((ModuleCat.extendScalars (RingedStalk.analytificationRingedStalkMap X p)).obj
        ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of X.left) X.left.ringCatSheaf
          (Base.analytificationMap X p)).obj M)) :=
  (ModuleStalk.analytificationModuleStalkIso Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).inv.app
      ((Scheme.Modules.pushforward f.left).obj M) ≫
    (StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
      (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).map
        ((Pushforward.moduleAnalytificationPushforwardComparison f).app M) ≫
    SchemeModuleStalkPullback.holomorphicModulePushforwardStalkHom f p ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M) ≫
    (ModuleCat.restrictScalars (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback f p)).map
      ((ModuleStalk.analytificationModuleStalkIso X p).hom.app M)

theorem moduleAnalytificationStalkComparison_apply_hom (M : X.left.Modules)
    (v : (StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
      (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).obj
      ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification Y).obj
        ((Scheme.Modules.pushforward f.left).obj M))) :
    moduleAnalytificationStalkComparison f p M
      ((ModuleStalk.analytificationModuleStalkIso Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).hom.app
        ((Scheme.Modules.pushforward f.left).obj M) v) =
    (ModuleStalk.analytificationModuleStalkIso X p).hom.app M
      (SchemeModuleStalkPullback.holomorphicModulePushforwardStalkHom f p ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M)
        ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
          (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).map
            ((Pushforward.moduleAnalytificationPushforwardComparison f).app M) v)) := by
  let eY := (ModuleStalk.analytificationModuleStalkIso Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).app
    ((Scheme.Modules.pushforward f.left).obj M)
  change (ModuleStalk.analytificationModuleStalkIso X p).hom.app M
    (SchemeModuleStalkPullback.holomorphicModulePushforwardStalkHom f p ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M)
      ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
        (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).map
          ((Pushforward.moduleAnalytificationPushforwardComparison f).app M) (eY.inv (eY.hom v)))) = _
  exact congrArg (fun w => (ModuleStalk.analytificationModuleStalkIso X p).hom.app M
    (SchemeModuleStalkPullback.holomorphicModulePushforwardStalkHom f p ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M)
      ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
        (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).map
          ((Pushforward.moduleAnalytificationPushforwardComparison f).app M) w))) (Iso.hom_inv_id_apply eY v)

end

/-! The tensor-coordinate comparison is normalized on every original algebraic stalk element. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

theorem moduleAnalytificationStalkComparison_unit_germ
    (M : X.left.Modules) (U : Y.left.Opens)
    (hpU : Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) ∈ U)
    (m : M.val.obj (op (f.left ⁻¹ᵁ U))) :
    moduleAnalytificationStalkComparison f p M
      ((ModuleCat.extendRestrictScalarsAdj
        (RingedStalk.analytificationRingedStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p))).unit.app _
        (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := TopCat.of Y.left)
          ((Scheme.Modules.pushforward f.left).obj M).val.presheaf U
          (Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)) hpU m)) =
    (ModuleCat.extendRestrictScalarsAdj (RingedStalk.analytificationRingedStalkMap X p)).unit.app
      ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of X.left) X.left.ringCatSheaf
        (Base.analytificationMap X p)).obj M)
      (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := TopCat.of X.left)
        M.val.presheaf (f.left ⁻¹ᵁ U) (Base.analytificationMap X p) hpU m) := by
  have hY := StalkUnitNormalization.analytificationModuleStalkIso_germ_unit Y
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) ((Scheme.Modules.pushforward f.left).obj M) U hpU m
  have hC := moduleAnalytificationStalkComparison_apply_hom f p M
    (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
      ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification Y).obj
        ((Scheme.Modules.pushforward f.left).obj M)).val.presheaf
      (Open.AffineIsoEvaluation.analyticOpen Y U) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) hpU
      ((((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction Y).unit.app
        ((Scheme.Modules.pushforward f.left).obj M)).val.app (op U)) m))
  have hG := PushforwardUnitGerms.moduleAnalytificationPushforwardComparison_unit_germ f p M U hpU m
  have hX := StalkUnitNormalization.analytificationModuleStalkIso_germ_unit X p M (f.left ⁻¹ᵁ U) hpU m
  exact (congrArg (moduleAnalytificationStalkComparison f p M) hY).symm.trans
    (hC.trans ((congrArg ((ModuleStalk.analytificationModuleStalkIso X p).hom.app M) hG).trans hX))

theorem moduleAnalytificationStalkComparison_unit (M : X.left.Modules)
    (v : (StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of Y.left) Y.left.ringCatSheaf
      (Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p))).obj
        ((Scheme.Modules.pushforward f.left).obj M)) :
    moduleAnalytificationStalkComparison f p M
      ((ModuleCat.extendRestrictScalarsAdj
        (RingedStalk.analytificationRingedStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p))).unit.app _ v) =
    (ModuleCat.extendRestrictScalarsAdj (RingedStalk.analytificationRingedStalkMap X p)).unit.app
      ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of X.left) X.left.ringCatSheaf
        (Base.analytificationMap X p)).obj M)
      (SchemeModuleStalkPullback.algebraicModulePushforwardStalkHom f p M v) := by
  obtain ⟨U, hpU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat)
    (X := TopCat.of Y.left) ((Scheme.Modules.pushforward f.left).obj M).val.presheaf v
  exact (moduleAnalytificationStalkComparison_unit_germ f p M U hpU m).trans
    (congrArg ((ModuleCat.extendRestrictScalarsAdj (RingedStalk.analytificationRingedStalkMap X p)).unit.app
      ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of X.left) X.left.ringCatSheaf
        (Base.analytificationMap X p)).obj M))
      (SchemeModuleStalkPullback.algebraicModulePushforwardStalkHom_germ f p M U hpU m).symm)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytification.Stalk
