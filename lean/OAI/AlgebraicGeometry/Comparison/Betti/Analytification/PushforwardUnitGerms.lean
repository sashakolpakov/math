import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.Pushforward
import OAI.AlgebraicGeometry.Comparison.Betti.SchemeModuleStalkPullback

/-! # Pushforward Unit Germs -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytification.PushforwardUnitGerms

noncomputable section

/-! The actual sheaf comparison carries germs of the original analytification unit to the original source unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y)

theorem moduleAnalytificationPushforwardComparison_unit_sections
    (M : X.left.Modules) (U : Y.left.Opens) (m : M.val.obj (op (f.left ⁻¹ᵁ U))) :
    (((Pushforward.moduleAnalytificationPushforwardComparison f).app M).val.app (op (Open.AffineIsoEvaluation.analyticOpen Y U)))
      ((((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction Y).unit.app
        ((Scheme.Modules.pushforward f.left).obj M)).val.app (op U)) m) =
      (((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X).unit.app M).val.app
        (op (f.left ⁻¹ᵁ U))) m := by
  have h := congrArg (fun k : (Scheme.Modules.pushforward f.left).obj M ⟶
      (Holomorphic.StructureMorphism.holomorphicModuleDirectImage Y).obj
        ((Holomorphic.ModulePushforwardSquare.analyticHolomorphicModulePushforward f).obj
          ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M)) => k.val.app (op U) m)
    (Pushforward.moduleAnalytificationPushforwardComparison_unit f M)
  exact h.trans (Pushforward.moduleAnalytificationPushforwardUnit_sections f M U m)

theorem moduleAnalytificationPushforwardComparison_unit_germ
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (M : X.left.Modules) (U : Y.left.Opens)
    (hpU : Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) ∈ U)
    (m : M.val.obj (op (f.left ⁻¹ᵁ U))) :
    SchemeModuleStalkPullback.holomorphicModulePushforwardStalkHom f p ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M)
      ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
        (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).map
          ((Pushforward.moduleAnalytificationPushforwardComparison f).app M)
        (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
          ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification Y).obj
            ((Scheme.Modules.pushforward f.left).obj M)).val.presheaf
          (Open.AffineIsoEvaluation.analyticOpen Y U) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) hpU
          ((((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction Y).unit.app
            ((Scheme.Modules.pushforward f.left).obj M)).val.app (op U)) m))) =
      TopCat.Presheaf.germ (C := AddCommGrpCat) (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf
        (Open.AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U)) p hpU
        ((((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X).unit.app M).val.app
          (op (f.left ⁻¹ᵁ U))) m) := by
  change SchemeModuleStalkPullback.holomorphicModulePushforwardStalkHom f p ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M)
    (RingModuleStalkMap.Local.ringModuleStalkMap (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
      (R := (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y).obj)
      ((Pushforward.moduleAnalytificationPushforwardComparison f).app M).val
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) _) = _
  erw [RingModuleStalkMap.Local.ringModuleStalkMap_germ, SchemeModuleStalkPullback.holomorphicModulePushforwardStalkHom_germ]
  exact congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat)
    (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf
    (Open.AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U)) p hpU)
    (moduleAnalytificationPushforwardComparison_unit_sections f M U m)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytification.PushforwardUnitGerms
