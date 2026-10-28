import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullbackSpec
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackScalarsValue

/-! # Tensor Pullback Unit -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullbackUnit.Construction.TensorPullbackMap

noncomputable section

/-! The tensor-power pullback comparison on trivialized line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

universe u

variable {X Y : Scheme.{u}}

theorem unit_compatibility (f : X ⟶ Y) (n : ℕ) :
    TensorPullbackSpec.Construction.TensorPullbackMap.comparison f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) n ≫
        AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom n ≫ (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerUnitIso X n).hom =
      (Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerUnitIso Y n).hom ≫
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom := by
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  let j : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pushforward f).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have he : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom = j :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hX : (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) n).postcomp
      (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerUnitIso X n).hom = AbelianModuli.HilbertConstruction.LineBundle.Powers.structureModuleTensorMap X n := AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerUnitHom_spec X n
  have hY : (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) n).postcomp
      (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerUnitIso Y n).hom = AbelianModuli.HilbertConstruction.LineBundle.Powers.structureModuleTensorMap Y n := AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerUnitHom_spec Y n
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    TensorPullbackSpec.Construction.TensorPullbackMap.homEquiv_comparison, he]
  apply AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPower_hom_ext
  rw [AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp, TensorPullbackSpec.Construction.TensorPullbackMap.adjunct_spec,
    ← AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_postcomp, ← AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.pushforward_postcomp,
    AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp, AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap_spec,
    ← AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_postcomp, hX,
    AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.pushforward_precomp, AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_comp,
    AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp, hY]
  change ((AbelianModuli.HilbertConstruction.LineBundle.Powers.structureModuleTensorMap X n).pushforward f).precomp
      (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom) = _
  rw [he]
  apply AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.ext
  intro U
  apply MultilinearMap.ext
  intro s
  change Fin n → Γ(Y, U) at s
  change (∏ i, f.app U (s i)) = f.app U (∏ i, s i)
  exact (map_prod (f.app U).hom s Finset.univ).symm

theorem unit_isIso (f : X ⟶ Y) (n : ℕ) :
    IsIso (TensorPullbackSpec.Construction.TensorPullbackMap.comparison f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) n) := by
  have : IsIso (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom n) :=
    (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerFunctor X n).map_isIso _
  have h : IsIso (TensorPullbackSpec.Construction.TensorPullbackMap.comparison f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) n ≫
      AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom n ≫ (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerUnitIso X n).hom) :=
    (unit_compatibility f n).symm ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp h

theorem isIso_of_frame (f : X ⟶ Y) {L : Y.Modules}
    (e : L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (n : ℕ) : IsIso (TensorPullbackSpec.Construction.TensorPullbackMap.comparison f L n) := by
  have : IsIso (TensorPullbackSpec.Construction.TensorPullbackMap.comparison f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) n) := unit_isIso f n
  have : IsIso (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap e.hom n) := (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerFunctor Y n).map_isIso _
  have : IsIso (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullback f).map e.hom) n) :=
    (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerFunctor X n).map_isIso _
  have h : IsIso (TensorPullbackSpec.Construction.TensorPullbackMap.comparison f L n ≫ AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullback f).map e.hom) n) :=
    (TensorPullbackSpec.Construction.TensorPullbackMap.naturality f e.hom n) ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp h

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullbackUnit.Construction.TensorPullbackMap
