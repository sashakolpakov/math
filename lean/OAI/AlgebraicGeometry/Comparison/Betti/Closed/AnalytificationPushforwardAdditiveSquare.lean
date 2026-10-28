import OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.Module
import OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationAdditiveUnit

/-! # Analytification Pushforward Additive Square -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Closed.AnalytificationPushforwardAdditiveSquare

noncomputable section

section

/-! The original global-section comparison descends from the ambient scheme along a closed immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

def moduleAnalytificationGlobalSectionsMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral X.left] [Smooth X.hom] (M : X.left.Modules) :
    M.val.presheaf.obj (op ⊤) ⟶
      ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf.obj (op ⊤) :=
  (Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X M).app (op ⊤)

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y)

theorem moduleAnalytificationGlobalSectionsMap_pushforward (M : X.left.Modules) :
    moduleAnalytificationGlobalSectionsMap X M =
      moduleAnalytificationGlobalSectionsMap Y ((Scheme.Modules.pushforward f.left).obj M) ≫
        (((SheafOfModules.toSheaf (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y)).map
          ((Analytification.Pushforward.moduleAnalytificationPushforwardComparison f).app M)).hom.app (op ⊤)) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro m
  exact (Analytification.PushforwardUnitGerms.moduleAnalytificationPushforwardComparison_unit_sections f M ⊤ m).symm

theorem moduleAnalytificationGlobalSectionsMap_isIso_closed [IsClosedImmersion f.left]
    (M : X.left.Modules)
    (hM : IsIso (moduleAnalytificationGlobalSectionsMap Y
      ((Scheme.Modules.pushforward f.left).obj M))) :
    IsIso (moduleAnalytificationGlobalSectionsMap X M) := by
  have := hM
  let F := SheafOfModules.toSheaf (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y) ⋙
    TopCat.Sheaf.forget AddCommGrpCat (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⋙
      (CategoryTheory.evaluation _ AddCommGrpCat).obj (op ⊤)
  let e := F.mapIso ((ClosedImmersion.Module.moduleAnalytificationClosedPushforwardIso f).app M)
  let E := asIso (moduleAnalytificationGlobalSectionsMap Y
    ((Scheme.Modules.pushforward f.left).obj M)) ≪≫ e
  have he : moduleAnalytificationGlobalSectionsMap X M = E.hom :=
    moduleAnalytificationGlobalSectionsMap_pushforward f M
  exact he.symm ▸ E.isIso_hom

end

/-! The original module units and the actual pushforward comparison commute after forgetting scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y)

def moduleAnalytificationPushforwardAdditiveMap (M : X.left.Modules) :
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification Y).obj
      ((Scheme.Modules.pushforward f.left).obj M)).val.presheaf ⟶
      (Opens.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).op ⋙
        ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf :=
  ((SheafOfModules.toSheaf (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y)).map
    ((Analytification.Pushforward.moduleAnalytificationPushforwardComparison f).app M)).hom

theorem moduleAnalytificationPushforwardAdditiveSquare (M : X.left.Modules) :
    Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit Y ((Scheme.Modules.pushforward f.left).obj M) ≫
      Functor.whiskerLeft (Opens.map (Analytification.Base.analytificationMap Y)).op
        (moduleAnalytificationPushforwardAdditiveMap f M) =
    Functor.whiskerLeft (Opens.map f.left.base).op (Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X M) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro m
  exact Analytification.PushforwardUnitGerms.moduleAnalytificationPushforwardComparison_unit_sections f M U.unop m

end

end OAI.AlgebraicGeometry.Comparison.Betti.Closed.AnalytificationPushforwardAdditiveSquare
