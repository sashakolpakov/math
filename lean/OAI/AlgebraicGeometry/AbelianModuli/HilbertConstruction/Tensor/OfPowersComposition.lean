import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.FrameNaturality

/-! # Of Powers Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.OfPowersComposition

noncomputable section

/-! Compatibility of the tensor-of-powers pullback comparison with composite open immersions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem tensorOfPowersPullbackIso_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (L M : Z.Modules) (n : ℕ) :
    (Scheme.Modules.pullback f).map (TensorPower.ProductPullbacks.tensorOfPowersPullbackIso g L M n).hom ≫
      (TensorPower.ProductPullbacks.tensorOfPowersPullbackIso f ((Scheme.Modules.pullback g).obj L)
        ((Scheme.Modules.pullback g).obj M) n).hom ≫
      Bifunctor.tensorModuleMap (TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullbackComp f g).hom.app L) n)
        (TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullbackComp f g).hom.app M) n) =
      (Scheme.Modules.pullbackComp f g).hom.app
        (ProductSheaf.tensorModule (TensorPower.PowerSheaf.tensorPowerModule L n) (TensorPower.PowerSheaf.tensorPowerModule M n)) ≫
        (TensorPower.ProductPullbacks.tensorOfPowersPullbackIso (f ≫ g) L M n).hom := by
  change (Scheme.Modules.pullback f).map
      (PullbackComparison.tensorPullbackComparison g (TensorPower.PowerSheaf.tensorPowerModule L n) (TensorPower.PowerSheaf.tensorPowerModule M n) ≫
        Bifunctor.tensorModuleMap (Power.PullbackComparison.powerPullbackComparison g L n) (Power.PullbackComparison.powerPullbackComparison g M n)) ≫
    (PullbackComparison.tensorPullbackComparison f (TensorPower.PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback g).obj L) n)
      (TensorPower.PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback g).obj M) n) ≫
      Bifunctor.tensorModuleMap (Power.PullbackComparison.powerPullbackComparison f ((Scheme.Modules.pullback g).obj L) n)
        (Power.PullbackComparison.powerPullbackComparison f ((Scheme.Modules.pullback g).obj M) n)) ≫ _ =
    _ ≫ (PullbackComparison.tensorPullbackComparison (f ≫ g) (TensorPower.PowerSheaf.tensorPowerModule L n) (TensorPower.PowerSheaf.tensorPowerModule M n) ≫
      Bifunctor.tensorModuleMap (Power.PullbackComparison.powerPullbackComparison (f ≫ g) L n) (Power.PullbackComparison.powerPullbackComparison (f ≫ g) M n))
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback f).map
    (Bifunctor.tensorModuleMap (Power.PullbackComparison.powerPullbackComparison g L n) (Power.PullbackComparison.powerPullbackComparison g M n))),
    PullbackComparison.tensorPullbackComparison_natural]
  simp only [Category.assoc]
  rw [Bifunctor.tensorModuleMap_comp, Bifunctor.tensorModuleMap_comp, Power.PullbackComposition.powerPullbackComparison_comp,
    Power.PullbackComposition.powerPullbackComparison_comp, ← Bifunctor.tensorModuleMap_comp]
  rw [← Category.assoc (PullbackComparison.tensorPullbackComparison f
    ((Scheme.Modules.pullback g).obj (TensorPower.PowerSheaf.tensorPowerModule L n))
    ((Scheme.Modules.pullback g).obj (TensorPower.PowerSheaf.tensorPowerModule M n))),
    ← Category.assoc ((Scheme.Modules.pullback f).map
    (PullbackComparison.tensorPullbackComparison g (TensorPower.PowerSheaf.tensorPowerModule L n) (TensorPower.PowerSheaf.tensorPowerModule M n))),
    PullbackComposition.tensorPullbackComparison_comp]
  exact Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.OfPowersComposition
