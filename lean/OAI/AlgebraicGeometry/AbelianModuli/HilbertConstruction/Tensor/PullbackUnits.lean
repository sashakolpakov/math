import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackComparison

/-! # Pullback Units -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackUnits

noncomputable section

/-! The arbitrary-pullback tensor comparison is invertible for trivial factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

def unitLeftBilinear (M : X.Modules) : Bilinear.Sheaves.SheafBilinearMap (Line.Bundles.structureModule X) M M where
  app U := LinearMap.lsmul Γ(X, U) Γ(M, U)
  naturality h r m := M.val.map_smul h.op r m

theorem tensorModuleUnitLeftIso_formula (M : X.Modules) :
    Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (Line.Bundles.structureModule X) M M
      (ProductSheaf.tensorModuleUnitLeftIso M).hom = unitLeftBilinear M := by
  let a : PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
      (Line.Bundles.structureModule X).val M.val ⟶ M.val := (λ_ M.val).hom
  have h : ProductSheaf.tensorModuleHomEquiv (Line.Bundles.structureModule X) M M
      (ProductSheaf.tensorModuleUnitLeftIso M).hom = a := by
    exact ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ M).apply_symm_apply a
  change Bilinear.Sheaves.SheafBilinearMap.ofTensorPresheafHom
    (ProductSheaf.tensorModuleHomEquiv (Line.Bundles.structureModule X) M M (ProductSheaf.tensorModuleUnitLeftIso M).hom) = _
  rw [h]
  ext U
  rfl

theorem structureModulePullbackIso_unit (f : X ⟶ Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (Line.Bundles.structureModule Y) ≫
      (Scheme.Modules.pushforward f).map (Line.Bundles.structureModulePullbackIso f).hom =
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom

theorem unitLeftBilinear_pushforward (f : X ⟶ Y) :
    ((unitLeftBilinear (Line.Bundles.structureModule X)).pushforward f).precomp
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) =
      (unitLeftBilinear (Line.Bundles.structureModule Y)).postcomp
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  apply Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply DFunLike.ext
  intro r
  apply DFunLike.ext
  intro s
  change Γ(Y, U) at r s
  exact (map_mul (f.app U).hom r s).symm

theorem tensorPullbackComparison_unit_formula (f : X ⟶ Y) :
    PullbackComparison.tensorPullbackComparison f (Line.Bundles.structureModule Y) (Line.Bundles.structureModule Y) ≫
      Bifunctor.tensorModuleMap (Line.Bundles.structureModulePullbackIso f).hom (Line.Bundles.structureModulePullbackIso f).hom ≫
        (ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule X)).hom =
      (Scheme.Modules.pullback f).map (ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule Y)).hom ≫
        (Line.Bundles.structureModulePullbackIso f).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (Line.Bundles.structureModule Y) (Line.Bundles.structureModule Y) _).injective
  rw [(Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right,
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left,
    Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, PullbackComparison.tensorPullbackComparison_spec,
    ← PullbackComparison.bilinearPullbackUnit_postcomp, Bilinear.Sheaves.SheafBilinearMap.postcomp_comp,
    Bifunctor.tensorModuleMap_spec, ← Bilinear.Sheaves.SheafBilinearMap.precomp_postcomp, Bifunctor.tensorBilinear_postcomp,
    tensorModuleUnitLeftIso_formula]
  unfold PullbackComparison.bilinearPullbackUnit
  rw [Bilinear.Sheaves.SheafBilinearMap.pushforward_precomp, Bilinear.Sheaves.SheafBilinearMap.precomp_comp,
    structureModulePullbackIso_unit, unitLeftBilinear_pushforward]
  rw [Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, tensorModuleUnitLeftIso_formula]
  exact congrArg (fun a => (unitLeftBilinear (Line.Bundles.structureModule Y)).postcomp a)
    (structureModulePullbackIso_unit f).symm

instance tensorPullbackComparison_unit_isIso (f : X ⟶ Y) :
    IsIso (PullbackComparison.tensorPullbackComparison f (Line.Bundles.structureModule Y) (Line.Bundles.structureModule Y)) := by
  have h : IsIso (PullbackComparison.tensorPullbackComparison f (Line.Bundles.structureModule Y) (Line.Bundles.structureModule Y) ≫
      Bifunctor.tensorModuleMap (Line.Bundles.structureModulePullbackIso f).hom (Line.Bundles.structureModulePullbackIso f).hom ≫
        (ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule X)).hom) := by
    rw [tensorPullbackComparison_unit_formula]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackUnits
