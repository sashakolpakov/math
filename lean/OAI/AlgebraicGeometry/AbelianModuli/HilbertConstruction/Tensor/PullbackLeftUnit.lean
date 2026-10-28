import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackUnits

/-! # Pullback Left Unit -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackLeftUnit

noncomputable section

/-! The canonical tensor pullback comparison is invertible when its left factor is the structure sheaf and its right factor is arbitrary. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

theorem unitLeftBilinear_pushforward_map (f : X ⟶ Y) (M : Y.Modules) (P : X.Modules)
    (h : M ⟶ (Scheme.Modules.pushforward f).obj P) :
    ((PullbackUnits.unitLeftBilinear P).pushforward f).precomp
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) h =
      (PullbackUnits.unitLeftBilinear M).postcomp h := by
  apply Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply DFunLike.ext
  intro r
  apply DFunLike.ext
  intro m
  exact ((Powers.SheafMultilinearMap.homApp h U).map_smul r m).symm

theorem tensorPullbackComparison_leftUnit_formula (f : X ⟶ Y) (M : Y.Modules) :
    PullbackComparison.tensorPullbackComparison f (Line.Bundles.structureModule Y) M ≫
      Bifunctor.tensorModuleMap (Line.Bundles.structureModulePullbackIso f).hom
        (𝟙 ((Scheme.Modules.pullback f).obj M)) ≫
      (ProductSheaf.tensorModuleUnitLeftIso ((Scheme.Modules.pullback f).obj M)).hom =
      (Scheme.Modules.pullback f).map (ProductSheaf.tensorModuleUnitLeftIso M).hom := by
  rw [← Category.comp_id ((Scheme.Modules.pullback f).map (ProductSheaf.tensorModuleUnitLeftIso M).hom)]
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (Line.Bundles.structureModule Y) M _).injective
  rw [(Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right,
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left,
    Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, PullbackComparison.tensorPullbackComparison_spec,
    ← PullbackComparison.bilinearPullbackUnit_postcomp, Bilinear.Sheaves.SheafBilinearMap.postcomp_comp,
    Bifunctor.tensorModuleMap_spec, ← Bilinear.Sheaves.SheafBilinearMap.precomp_postcomp, Bifunctor.tensorBilinear_postcomp,
    PullbackUnits.tensorModuleUnitLeftIso_formula]
  unfold PullbackComparison.bilinearPullbackUnit
  rw [Bilinear.Sheaves.SheafBilinearMap.pushforward_precomp, Bilinear.Sheaves.SheafBilinearMap.precomp_comp,
    PullbackUnits.structureModulePullbackIso_unit, (Scheme.Modules.pushforward f).map_id, Category.comp_id,
    unitLeftBilinear_pushforward_map]
  rw [Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, PullbackUnits.tensorModuleUnitLeftIso_formula]
  rfl

theorem tensorPullbackComparison_leftUnit_isIso (f : X ⟶ Y) (M : Y.Modules) :
    IsIso (PullbackComparison.tensorPullbackComparison f (Line.Bundles.structureModule Y) M) := by
  have h : IsIso (PullbackComparison.tensorPullbackComparison f (Line.Bundles.structureModule Y) M ≫
      Bifunctor.tensorModuleMap (Line.Bundles.structureModulePullbackIso f).hom
        (𝟙 ((Scheme.Modules.pullback f).obj M)) ≫
      (ProductSheaf.tensorModuleUnitLeftIso ((Scheme.Modules.pullback f).obj M)).hom) := by
    rw [tensorPullbackComparison_leftUnit_formula]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackLeftUnit
