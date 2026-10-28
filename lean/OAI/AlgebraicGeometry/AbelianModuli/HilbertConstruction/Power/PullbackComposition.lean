import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.PullbackOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.TensorCompositionUnits

/-! # Pullback Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Tensor-power pullback comparisons respect composition of scheme morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem Tensor.Powers.SheafMultilinearMap.pushforward_comp {L P : X.Modules} {n : ℕ}
    (β : Tensor.Powers.SheafMultilinearMap L n P) (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((β.pushforward f).pushforward g).postcomp
      ((Scheme.Modules.pushforwardComp f g).hom.app P) =
      (β.pushforward (f ≫ g)).precomp ((Scheme.Modules.pushforwardComp f g).hom.app L) := by
  ext U
  rfl

theorem Power.PullbackComposition.multilinearPullbackUnit_comp (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) (n : ℕ)
    (P : X.Modules) (β : Tensor.Powers.SheafMultilinearMap ((Scheme.Modules.pullback (f ≫ g)).obj L) n P) :
    (Power.PullbackComparison.multilinearPullbackUnit g L n ((Scheme.Modules.pushforward f).obj P)
      (Power.PullbackComparison.multilinearPullbackUnit f ((Scheme.Modules.pullback g).obj L) n P
        (β.precomp ((Scheme.Modules.pullbackComp f g).hom.app L)))).postcomp
      ((Scheme.Modules.pushforwardComp f g).hom.app P) =
      Power.PullbackComparison.multilinearPullbackUnit (f ≫ g) L n P β := by
  unfold Power.PullbackComparison.multilinearPullbackUnit
  rw [Tensor.Powers.SheafMultilinearMap.pushforward_precomp, Tensor.Powers.SheafMultilinearMap.pushforward_precomp,
    Tensor.Powers.SheafMultilinearMap.pushforward_precomp, Tensor.Powers.SheafMultilinearMap.precomp_comp,
    Tensor.Powers.SheafMultilinearMap.precomp_comp, ← Tensor.Powers.SheafMultilinearMap.precomp_postcomp,
    Tensor.Powers.SheafMultilinearMap.pushforward_comp, Tensor.Powers.SheafMultilinearMap.precomp_comp]
  apply congrArg (fun a => (β.pushforward (f ≫ g)).precomp a)
  simpa only [Functor.map_comp, Category.assoc] using Pullback.TensorCompositionUnits.pullbackComp_hom_unit f g L

theorem Power.PullbackComposition.powerPullbackComparison_comp (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) (n : ℕ) :
    (Scheme.Modules.pullback f).map (Power.PullbackComparison.powerPullbackComparison g L n) ≫
      Power.PullbackComparison.powerPullbackComparison f ((Scheme.Modules.pullback g).obj L) n ≫
      TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullbackComp f g).hom.app L) n =
      (Scheme.Modules.pullbackComp f g).hom.app (TensorPower.PowerSheaf.tensorPowerModule L n) ≫
        Power.PullbackComparison.powerPullbackComparison (f ≫ g) L n := by
  let P := TensorPower.PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback (f ≫ g)).obj L) n
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ P).injective
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _
    ((Scheme.Modules.pushforward f).obj P)).injective
  apply (cancel_mono ((Scheme.Modules.pushforwardComp f g).hom.app P)).mp
  apply (TensorPower.PowerSheaf.tensorPowerHomEquiv L _ n).injective
  rw [Pullback.TensorCompositionUnits.pullbackComp_homEquiv, Power.PullbackComparison.powerPullbackComparison_spec, TensorPower.PowerSheaf.tensorPowerHomEquiv_postcomp,
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left]
  let a := TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullbackComp f g).hom.app L) n
  have hf := Power.PullbackOpen.powerPullbackComparison_homEquiv f ((Scheme.Modules.pullback g).obj L) n P a
  have hg := Power.PullbackOpen.powerPullbackComparison_homEquiv g L n ((Scheme.Modules.pushforward f).obj P)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ P
      (Power.PullbackComparison.powerPullbackComparison f ((Scheme.Modules.pullback g).obj L) n ≫ a))
  have ha : TensorPower.PowerSheaf.tensorPowerHomEquiv _ P n a =
      (TensorPower.Maps.tensorPowerMultilinear ((Scheme.Modules.pullback (f ≫ g)).obj L) n).precomp
        ((Scheme.Modules.pullbackComp f g).hom.app L) :=
    (TensorPower.Maps.tensorPowerMultilinear_postcomp a).symm.trans (TensorPower.Maps.tensorPowerMap_spec _ n)
  exact (congrArg (fun β => β.postcomp ((Scheme.Modules.pushforwardComp f g).hom.app P)) hg).trans
    ((congrArg (fun β => (Power.PullbackComparison.multilinearPullbackUnit g L n ((Scheme.Modules.pushforward f).obj P) β).postcomp
      ((Scheme.Modules.pushforwardComp f g).hom.app P)) hf).trans
      ((congrArg (fun β => (Power.PullbackComparison.multilinearPullbackUnit g L n ((Scheme.Modules.pushforward f).obj P)
        (Power.PullbackComparison.multilinearPullbackUnit f ((Scheme.Modules.pullback g).obj L) n P β)).postcomp
          ((Scheme.Modules.pushforwardComp f g).hom.app P)) ha).trans
        (Power.PullbackComposition.multilinearPullbackUnit_comp f g L n P _)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
