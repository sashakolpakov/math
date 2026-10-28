import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultilinearRestriction

/-! # Pullback Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.PullbackComparison

noncomputable section

/-! Canonical comparison of tensor powers with arbitrary pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem tensorPowerHomEquiv_precomp {L M P : Y.Modules} (a : L ⟶ M) (n : ℕ)
    (h : TensorPower.PowerSheaf.tensorPowerModule M n ⟶ P) :
    TensorPower.PowerSheaf.tensorPowerHomEquiv L P n (TensorPower.Maps.tensorPowerMap a n ≫ h) =
      (TensorPower.PowerSheaf.tensorPowerHomEquiv M P n h).precomp a := by
  rw [← TensorPower.Maps.tensorPowerMultilinear_postcomp, Tensor.Powers.SheafMultilinearMap.postcomp_comp,
    TensorPower.Maps.tensorPowerMap_spec, ← Tensor.Powers.SheafMultilinearMap.precomp_postcomp,
    TensorPower.Maps.tensorPowerMultilinear_postcomp]

def multilinearPullbackUnit (f : X ⟶ Y) (L : Y.Modules) (n : ℕ) (P : X.Modules)
    (β : Tensor.Powers.SheafMultilinearMap ((Scheme.Modules.pullback f).obj L) n P) :
    Tensor.Powers.SheafMultilinearMap L n ((Scheme.Modules.pushforward f).obj P) :=
  (β.pushforward f).precomp ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L)

theorem multilinearPullbackUnit_postcomp (f : X ⟶ Y) (L : Y.Modules) (n : ℕ)
    {P Q : X.Modules} (β : Tensor.Powers.SheafMultilinearMap ((Scheme.Modules.pullback f).obj L) n P)
    (h : P ⟶ Q) :
    multilinearPullbackUnit f L n Q (β.postcomp h) =
      (multilinearPullbackUnit f L n P β).postcomp ((Scheme.Modules.pushforward f).map h) := by
  exact (congrArg (fun γ => γ.precomp
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L))
      (β.pushforward_postcomp f h)).trans (Tensor.Powers.SheafMultilinearMap.precomp_postcomp _ _ _)

theorem multilinearPullbackUnit_precomp (f : X ⟶ Y) {L M : Y.Modules} (n : ℕ)
    (P : X.Modules) (β : Tensor.Powers.SheafMultilinearMap ((Scheme.Modules.pullback f).obj M) n P)
    (a : L ⟶ M) :
    multilinearPullbackUnit f L n P (β.precomp ((Scheme.Modules.pullback f).map a)) =
      (multilinearPullbackUnit f M n P β).precomp a := by
  unfold multilinearPullbackUnit
  rw [Tensor.Powers.SheafMultilinearMap.pushforward_precomp, Tensor.Powers.SheafMultilinearMap.precomp_comp,
    Tensor.Powers.SheafMultilinearMap.precomp_comp]
  exact congrArg (fun c => (β.pushforward f).precomp c)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a).symm

def powerPullbackComparison (f : X ⟶ Y) (L : Y.Modules) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule L n) ⟶
      TensorPower.PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback f).obj L) n :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    ((TensorPower.PowerSheaf.tensorPowerHomEquiv L _ n).symm
      (multilinearPullbackUnit f L n _
        (TensorPower.Maps.tensorPowerMultilinear ((Scheme.Modules.pullback f).obj L) n)))

theorem powerPullbackComparison_spec (f : X ⟶ Y) (L : Y.Modules) (n : ℕ) :
    TensorPower.PowerSheaf.tensorPowerHomEquiv L _ n
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (powerPullbackComparison f L n)) =
      multilinearPullbackUnit f L n _
        (TensorPower.Maps.tensorPowerMultilinear ((Scheme.Modules.pullback f).obj L) n) := by
  unfold powerPullbackComparison
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem powerPullbackComparison_natural (f : X ⟶ Y) {L M : Y.Modules} (a : L ⟶ M) (n : ℕ) :
    (Scheme.Modules.pullback f).map (TensorPower.Maps.tensorPowerMap a n) ≫ powerPullbackComparison f M n =
      powerPullbackComparison f L n ≫ TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullback f).map a) n := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply (TensorPower.PowerSheaf.tensorPowerHomEquiv L _ n).injective
  rw [(Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left,
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right,
    tensorPowerHomEquiv_precomp, TensorPower.PowerSheaf.tensorPowerHomEquiv_postcomp,
    powerPullbackComparison_spec, powerPullbackComparison_spec,
    ← multilinearPullbackUnit_postcomp, TensorPower.Maps.tensorPowerMap_spec,
    multilinearPullbackUnit_precomp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.PullbackComparison
