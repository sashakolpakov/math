import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.PullbackComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackUnits

/-! # Pullback Units -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.PullbackUnits

noncomputable section

/-! Arbitrary pullback commutes with tensor powers of the structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

universe u

variable {X Y : Scheme.{u}}

theorem structureModuleTensorMap_pushforward (f : X ⟶ Y) (n : ℕ) :
    ((LineBundle.Powers.structureModuleTensorMap X n).pushforward f).precomp
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) =
      (LineBundle.Powers.structureModuleTensorMap Y n).postcomp
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  apply Tensor.Powers.SheafMultilinearMap.ext
  intro U
  apply DFunLike.ext
  intro s
  change (Fin n → Γ(Y, U)) at s
  exact (map_prod (f.app U).hom s Finset.univ).symm

theorem powerPullbackComparison_unit_formula (f : X ⟶ Y) (n : ℕ) :
    PullbackComparison.powerPullbackComparison f (Line.Bundles.structureModule Y) n ≫
      TensorPower.Maps.tensorPowerMap (Line.Bundles.structureModulePullbackIso f).hom n ≫ (TensorPower.Maps.tensorPowerUnitIso X n).hom =
      (Scheme.Modules.pullback f).map (TensorPower.Maps.tensorPowerUnitIso Y n).hom ≫
        (Line.Bundles.structureModulePullbackIso f).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply (TensorPower.PowerSheaf.tensorPowerHomEquiv (Line.Bundles.structureModule Y) _ n).injective
  rw [(Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right,
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left,
    TensorPower.PowerSheaf.tensorPowerHomEquiv_postcomp, PullbackComparison.powerPullbackComparison_spec,
    ← PullbackComparison.multilinearPullbackUnit_postcomp, Tensor.Powers.SheafMultilinearMap.postcomp_comp,
    TensorPower.Maps.tensorPowerMap_spec, ← Tensor.Powers.SheafMultilinearMap.precomp_postcomp]
  have hX : (TensorPower.Maps.tensorPowerMultilinear (Line.Bundles.structureModule X) n).postcomp (TensorPower.Maps.tensorPowerUnitIso X n).hom =
      LineBundle.Powers.structureModuleTensorMap X n := TensorPower.Maps.tensorPowerUnitHom_spec X n
  rw [hX]
  unfold PullbackComparison.multilinearPullbackUnit
  rw [Tensor.Powers.SheafMultilinearMap.pushforward_precomp, Tensor.Powers.SheafMultilinearMap.precomp_comp,
    Tensor.PullbackUnits.structureModulePullbackIso_unit, structureModuleTensorMap_pushforward,
    TensorPower.PowerSheaf.tensorPowerHomEquiv_postcomp]
  have h : TensorPower.PowerSheaf.tensorPowerHomEquiv (Line.Bundles.structureModule Y) (Line.Bundles.structureModule Y) n
      (TensorPower.Maps.tensorPowerUnitIso Y n).hom = LineBundle.Powers.structureModuleTensorMap Y n :=
    (TensorPower.Maps.tensorPowerMultilinear_postcomp _).symm.trans (TensorPower.Maps.tensorPowerUnitHom_spec Y n)
  rw [h]
  exact congrArg (fun a => (LineBundle.Powers.structureModuleTensorMap Y n).postcomp a)
    (Tensor.PullbackUnits.structureModulePullbackIso_unit f).symm

instance powerPullbackComparison_unit_isIso (f : X ⟶ Y) (n : ℕ) :
    IsIso (PullbackComparison.powerPullbackComparison f (Line.Bundles.structureModule Y) n) := by
  have : IsIso (TensorPower.Maps.tensorPowerMap (Line.Bundles.structureModulePullbackIso f).hom n) :=
    (TensorPower.Maps.tensorPowerFunctor X n).map_isIso _
  have h : IsIso (PullbackComparison.powerPullbackComparison f (Line.Bundles.structureModule Y) n ≫
      TensorPower.Maps.tensorPowerMap (Line.Bundles.structureModulePullbackIso f).hom n ≫ (TensorPower.Maps.tensorPowerUnitIso X n).hom) := by
    rw [powerPullbackComparison_unit_formula]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.PullbackUnits
