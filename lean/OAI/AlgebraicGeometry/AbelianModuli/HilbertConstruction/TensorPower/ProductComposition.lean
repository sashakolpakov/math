import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.FrameNaturality

/-! # Product Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.ProductComposition

noncomputable section

/-! Compatibility of the power-of-tensor pullback comparison with composite open immersions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem tensorPowerOfTensorPullbackIso_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (L M : Z.Modules) (n : ℕ) :
    (Scheme.Modules.pullback f).map (ProductPullbacks.tensorPowerOfTensorPullbackIso g L M n).hom ≫
      (ProductPullbacks.tensorPowerOfTensorPullbackIso f ((Scheme.Modules.pullback g).obj L)
        ((Scheme.Modules.pullback g).obj M) n).hom ≫
      Maps.tensorPowerMap (Tensor.Bifunctor.tensorModuleMap ((Scheme.Modules.pullbackComp f g).hom.app L)
        ((Scheme.Modules.pullbackComp f g).hom.app M)) n =
      (Scheme.Modules.pullbackComp f g).hom.app (PowerSheaf.tensorPowerModule (Tensor.ProductSheaf.tensorModule L M) n) ≫
        (ProductPullbacks.tensorPowerOfTensorPullbackIso (f ≫ g) L M n).hom := by
  change (Scheme.Modules.pullback f).map
      (Power.PullbackComparison.powerPullbackComparison g (Tensor.ProductSheaf.tensorModule L M) n ≫ Maps.tensorPowerMap (Tensor.PullbackComparison.tensorPullbackComparison g L M) n) ≫
    (Power.PullbackComparison.powerPullbackComparison f (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback g).obj L)
      ((Scheme.Modules.pullback g).obj M)) n ≫
      Maps.tensorPowerMap (Tensor.PullbackComparison.tensorPullbackComparison f ((Scheme.Modules.pullback g).obj L)
        ((Scheme.Modules.pullback g).obj M)) n) ≫ _ =
    _ ≫ (Power.PullbackComparison.powerPullbackComparison (f ≫ g) (Tensor.ProductSheaf.tensorModule L M) n ≫
      Maps.tensorPowerMap (Tensor.PullbackComparison.tensorPullbackComparison (f ≫ g) L M) n)
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback f).map
    (Maps.tensorPowerMap (Tensor.PullbackComparison.tensorPullbackComparison g L M) n)), Power.PullbackComparison.powerPullbackComparison_natural]
  simp only [Category.assoc]
  rw [← Maps.tensorPowerMap_comp, ← Maps.tensorPowerMap_comp, Tensor.PullbackComposition.tensorPullbackComparison_comp,
    Maps.tensorPowerMap_comp]
  rw [← Category.assoc (Power.PullbackComparison.powerPullbackComparison f ((Scheme.Modules.pullback g).obj (Tensor.ProductSheaf.tensorModule L M)) n),
    ← Category.assoc ((Scheme.Modules.pullback f).map (Power.PullbackComparison.powerPullbackComparison g (Tensor.ProductSheaf.tensorModule L M) n)),
    Power.PullbackComposition.powerPullbackComparison_comp]
  exact Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.ProductComposition
