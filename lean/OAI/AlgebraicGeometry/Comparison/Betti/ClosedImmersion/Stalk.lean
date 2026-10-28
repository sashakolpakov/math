import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.Stalk
import OAI.AlgebraicGeometry.Comparison.Betti.ModuleBaseChangeIso

/-! # Stalk -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.Stalk

noncomputable section

section

/-! The actual analytification pushforward comparison is an isomorphism in tensor coordinates at every point of a smooth closed immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y) [IsClosedImmersion f.left]
  (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

theorem moduleAnalytificationStalkComparison_isIso (M : X.left.Modules) :
    IsIso (Analytification.Stalk.moduleAnalytificationStalkComparison f p M) := by
  let N := (StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of X.left) X.left.ringCatSheaf
    (Analytification.Base.analytificationMap X p)).obj M
  let a := Analytification.RingedStalk.analytificationRingedStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)
  let h := SchemeModuleStalkPullback.algebraicModulePushforwardStalkHom f p M
  have : IsIso h := (ConcreteCategory.isIso_iff_bijective h).mpr
    (SchemeModuleStalkPullback.algebraicModulePushforwardStalkHom_bijective f p M)
  obtain ⟨e, he⟩ := ModuleBaseChangeIso.closedImmersion_exists_stalkModuleBaseChangeIso f p N
  have hc : Analytification.Stalk.moduleAnalytificationStalkComparison f p M =
      (ModuleCat.extendScalars a).map h ≫ e.hom := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change Analytification.Stalk.moduleAnalytificationStalkComparison f p M
      ((ModuleCat.extendRestrictScalarsAdj a).unit.app _ m) =
      e.hom ((ModuleCat.extendRestrictScalarsAdj a).unit.app _ (h m))
    exact (Analytification.Stalk.moduleAnalytificationStalkComparison_unit f p M m).trans (he (h m)).symm
  have hg : IsIso ((ModuleCat.extendScalars a).map h ≫ e.hom) := inferInstance
  exact hc.symm ▸ hg

end

/-! At every embedded point, the stalk map of the original sheaf analytification comparison is an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y) [IsClosedImmersion f.left]

theorem moduleAnalytificationPushforwardComparison_stalk_isIso
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (M : X.left.Modules) :
    IsIso ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
      (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).map
        ((Analytification.Pushforward.moduleAnalytificationPushforwardComparison f).app M)) := by
  let k := (StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
    (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).map
      ((Analytification.Pushforward.moduleAnalytificationPushforwardComparison f).app M)
  let h := SchemeModuleStalkPullback.holomorphicModulePushforwardStalkHom f p
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M)
  let eY := (Analytification.ModuleStalk.analytificationModuleStalkIso Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).inv.app
    ((Scheme.Modules.pushforward f.left).obj M)
  let eX := (ModuleCat.restrictScalars (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback f p)).map
    ((Analytification.ModuleStalk.analytificationModuleStalkIso X p).hom.app M)
  have : IsIso eY := by
    change IsIso (((Analytification.ModuleStalk.analytificationModuleStalkIso Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).app
      ((Scheme.Modules.pushforward f.left).obj M)).inv)
    infer_instance
  have : IsIso eX := by
    change IsIso ((ModuleCat.restrictScalars (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback f p)).map
      (((Analytification.ModuleStalk.analytificationModuleStalkIso X p).app M).hom))
    infer_instance
  have : IsIso h := (ConcreteCategory.isIso_iff_bijective h).mpr
    (SchemeModuleStalkPullback.holomorphicModulePushforwardStalkHom_bijective f p
      ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M))
  have : IsIso (eY ≫ k ≫ h ≫ eX) := moduleAnalytificationStalkComparison_isIso f p M
  have : IsIso (k ≫ h ≫ eX) := IsIso.of_isIso_comp_left eY (k ≫ h ≫ eX)
  exact IsIso.of_isIso_comp_right k (h ≫ eX)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.Stalk
