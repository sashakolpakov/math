import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultilinearRestriction

/-! # Tensor Pullback Spec -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullbackSpec.Construction.TensorPullbackMap

noncomputable section

/-! The canonical comparison from pullback of a tensor power to the power of a pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps

universe u

variable {X Y : Scheme.{u}}

def adjunct (f : X ⟶ Y) (L : Y.Modules) (n : ℕ) :
    AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L n ⟶ (Scheme.Modules.pushforward f).obj
      (AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback f).obj L) n) :=
  (AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerHomEquiv L _ n).symm
    (((AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear ((Scheme.Modules.pullback f).obj L) n).pushforward f).precomp
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L))

theorem adjunct_spec (f : X ⟶ Y) (L : Y.Modules) (n : ℕ) :
    (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear L n).postcomp (adjunct f L n) =
      ((AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear ((Scheme.Modules.pullback f).obj L) n).pushforward f).precomp
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L) :=
  (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear_postcomp _).trans ((AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerHomEquiv L _ n).apply_symm_apply _)

def comparison (f : X ⟶ Y) (L : Y.Modules) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L n) ⟶
      AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback f).obj L) n :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (adjunct f L n)

theorem homEquiv_comparison (f : X ⟶ Y) (L : Y.Modules) (n : ℕ) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _) (comparison f L n) =
      adjunct f L n :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply _

theorem naturality (f : X ⟶ Y) {L M : Y.Modules} (h : L ⟶ M) (n : ℕ) :
    (Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap h n) ≫ comparison f M n =
      comparison f L n ≫ AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullback f).map h) n := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_comparison, homEquiv_comparison]
  apply AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPower_hom_ext
  rw [AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp, AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap_spec,
    ← AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_postcomp, adjunct_spec,
    AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_comp,
    AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp, adjunct_spec,
    ← AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_postcomp,
    ← AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.pushforward_postcomp, AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap_spec,
    AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.pushforward_precomp, AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_comp]
  exact congrArg (fun a =>
    ((AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear ((Scheme.Modules.pullback f).obj M) n).pushforward f).precomp a)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality h)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullbackSpec.Construction.TensorPullbackMap
