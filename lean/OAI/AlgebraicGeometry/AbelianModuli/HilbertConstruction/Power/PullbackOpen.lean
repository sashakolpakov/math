import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.PullbackComparison

/-! # Pullback Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.PullbackOpen

noncomputable section

/-! The tensor-power comparison is invertible on open immersions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

def multilinearOpenPullbackEquiv (f : X ⟶ Y) [IsOpenImmersion f] (L : Y.Modules)
    (n : ℕ) (P : X.Modules) :
    Tensor.Powers.SheafMultilinearMap ((Scheme.Modules.pullback f).obj L) n P ≃
      Tensor.Powers.SheafMultilinearMap L n ((Scheme.Modules.pushforward f).obj P) :=
  (Tensor.Powers.SheafMultilinearMap.sourceIso ((Scheme.Modules.restrictFunctorIsoPullback f).app L).symm
    n P).trans (Tensor.Powers.SheafMultilinearMap.restrictHomEquiv f L n P)

theorem multilinearOpenPullbackEquiv_apply (f : X ⟶ Y) [IsOpenImmersion f] (L : Y.Modules)
    (n : ℕ) (P : X.Modules) (β : Tensor.Powers.SheafMultilinearMap ((Scheme.Modules.pullback f).obj L) n P) :
    multilinearOpenPullbackEquiv f L n P β = PullbackComparison.multilinearPullbackUnit f L n P β := by
  change ((β.precomp ((Scheme.Modules.restrictFunctorIsoPullback f).app L).hom).pushforward f).precomp
    ((Scheme.Modules.restrictAdjunction f).unit.app L) = _
  rw [Tensor.Powers.SheafMultilinearMap.pushforward_precomp, Tensor.Powers.SheafMultilinearMap.precomp_comp]
  exact congrArg (fun a => (β.pushforward f).precomp a)
    ((Scheme.Modules.restrictAdjunction f).unit_leftAdjointUniq_hom_app
      (Scheme.Modules.pullbackPushforwardAdjunction f) L)

theorem powerPullbackComparison_homEquiv (f : X ⟶ Y) (L : Y.Modules) (n : ℕ) (P : X.Modules)
    (h : TensorPower.PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback f).obj L) n ⟶ P) :
    TensorPower.PowerSheaf.tensorPowerHomEquiv L _ n
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (PullbackComparison.powerPullbackComparison f L n ≫ h)) =
      PullbackComparison.multilinearPullbackUnit f L n P (TensorPower.PowerSheaf.tensorPowerHomEquiv _ P n h) := by
  rw [(Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right,
    TensorPower.PowerSheaf.tensorPowerHomEquiv_postcomp, PullbackComparison.powerPullbackComparison_spec,
    ← PullbackComparison.multilinearPullbackUnit_postcomp, TensorPower.Maps.tensorPowerMultilinear_postcomp]

theorem powerPullbackComparison_isIso_of_multilinearUnit (f : X ⟶ Y) (L : Y.Modules) (n : ℕ)
    (h : ∀ P : X.Modules, Function.Bijective (PullbackComparison.multilinearPullbackUnit f L n P)) :
    IsIso (PullbackComparison.powerPullbackComparison f L n) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro P
  let e := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ P).trans
    (TensorPower.PowerSheaf.tensorPowerHomEquiv L _ n)
  apply (e.bijective.of_comp_iff' _).mp
  change Function.Bijective (fun a => e (PullbackComparison.powerPullbackComparison f L n ≫ a))
  have he : (fun a => e (PullbackComparison.powerPullbackComparison f L n ≫ a)) =
      fun a => PullbackComparison.multilinearPullbackUnit f L n P (TensorPower.PowerSheaf.tensorPowerHomEquiv _ P n a) := by
    funext a
    exact powerPullbackComparison_homEquiv f L n P a
  rw [he]
  exact (h P).comp (TensorPower.PowerSheaf.tensorPowerHomEquiv _ P n).bijective

instance powerPullbackComparison_open_isIso (f : X ⟶ Y) [IsOpenImmersion f]
    (L : Y.Modules) (n : ℕ) : IsIso (PullbackComparison.powerPullbackComparison f L n) := by
  apply powerPullbackComparison_isIso_of_multilinearUnit
  intro P
  have h : PullbackComparison.multilinearPullbackUnit f L n P = multilinearOpenPullbackEquiv f L n P := by
    funext β
    exact (multilinearOpenPullbackEquiv_apply f L n P β).symm
  rw [h]
  exact (multilinearOpenPullbackEquiv f L n P).bijective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.PullbackOpen
