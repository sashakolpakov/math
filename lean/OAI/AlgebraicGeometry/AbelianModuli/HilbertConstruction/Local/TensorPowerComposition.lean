import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorPowerComparison

/-! # Tensor Power Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorPowerComposition

noncomputable section

/-! Local tensor-power isomorphisms agree after passing through a second open restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsOpenImmersion f] [IsOpenImmersion g] {L M : Z.Modules}
variable (e : Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback g).obj L)
variable (t : Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback g).obj M)
variable [IsIso e] [IsIso t] (n : ℕ)

theorem tensorPowerFrame_composite_transport :
    (Scheme.Modules.pullback f).map
      ((TensorPower.ProductPullbacks.tensorPowerOfTensorPullbackIso g L M n).hom ≫ (TensorPower.FrameComparison.tensorPowerFrameComparisonIso e t n).hom) ≫
      (TensorPower.ProductPullbacks.tensorOfPowersPullbackIso f ((Scheme.Modules.pullback g).obj L)
        ((Scheme.Modules.pullback g).obj M) n).hom ≫
      Tensor.Bifunctor.tensorModuleMap (TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullbackComp f g).hom.app L) n)
        (TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullbackComp f g).hom.app M) n) =
      (Scheme.Modules.pullbackComp f g).hom.app (TensorPower.PowerSheaf.tensorPowerModule (Tensor.ProductSheaf.tensorModule L M) n) ≫
        (TensorPower.ProductPullbacks.tensorPowerOfTensorPullbackIso (f ≫ g) L M n).hom ≫
        (TensorPower.FrameComparison.tensorPowerFrameComparisonIso
          (Ample.LineBundles.pullbackSection f e ≫ (Scheme.Modules.pullbackComp f g).hom.app L)
          (Ample.LineBundles.pullbackSection f t ≫ (Scheme.Modules.pullbackComp f g).hom.app M) n).hom := by
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback f).map (TensorPower.FrameComparison.tensorPowerFrameComparisonIso e t n).hom),
    TensorPower.FrameNaturality.tensorPowerFrameComparisonIso_pullback]
  simp only [Category.assoc]
  rw [← TensorPower.FrameNaturality.tensorPowerFrameComparisonIso_natural]
  rw [← Category.assoc (TensorPower.ProductPullbacks.tensorPowerOfTensorPullbackIso f ((Scheme.Modules.pullback g).obj L)
    ((Scheme.Modules.pullback g).obj M) n).hom,
    ← Category.assoc ((Scheme.Modules.pullback f).map (TensorPower.ProductPullbacks.tensorPowerOfTensorPullbackIso g L M n).hom),
    TensorPower.ProductComposition.tensorPowerOfTensorPullbackIso_comp]
  exact Category.assoc _ _ _

theorem localTensorPowerComparisonIso_comp :
    (Scheme.Modules.pullback f).map (TensorPowerComparison.localTensorPowerComparisonIso g e t n).hom ≫
      (Scheme.Modules.pullbackComp f g).hom.app
        (Tensor.ProductSheaf.tensorModule (TensorPower.PowerSheaf.tensorPowerModule L n) (TensorPower.PowerSheaf.tensorPowerModule M n)) =
      (Scheme.Modules.pullbackComp f g).hom.app (TensorPower.PowerSheaf.tensorPowerModule (Tensor.ProductSheaf.tensorModule L M) n) ≫
        (TensorPowerComparison.localTensorPowerComparisonIso (f ≫ g)
          (Ample.LineBundles.pullbackSection f e ≫ (Scheme.Modules.pullbackComp f g).hom.app L)
          (Ample.LineBundles.pullbackSection f t ≫ (Scheme.Modules.pullbackComp f g).hom.app M) n).hom := by
  apply (cancel_mono (TensorPower.ProductPullbacks.tensorOfPowersPullbackIso (f ≫ g) L M n).hom).mp
  calc
    _ = (Scheme.Modules.pullback f).map (TensorPowerComparison.localTensorPowerComparisonIso g e t n).hom ≫
        ((Scheme.Modules.pullback f).map (TensorPower.ProductPullbacks.tensorOfPowersPullbackIso g L M n).hom ≫
          (TensorPower.ProductPullbacks.tensorOfPowersPullbackIso f ((Scheme.Modules.pullback g).obj L)
            ((Scheme.Modules.pullback g).obj M) n).hom ≫
          Tensor.Bifunctor.tensorModuleMap (TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullbackComp f g).hom.app L) n)
            (TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullbackComp f g).hom.app M) n)) := by
      rw [Category.assoc, ← Tensor.OfPowersComposition.tensorOfPowersPullbackIso_comp]
    _ = (Scheme.Modules.pullback f).map
        ((TensorPowerComparison.localTensorPowerComparisonIso g e t n).hom ≫ (TensorPower.ProductPullbacks.tensorOfPowersPullbackIso g L M n).hom) ≫
          (TensorPower.ProductPullbacks.tensorOfPowersPullbackIso f ((Scheme.Modules.pullback g).obj L)
            ((Scheme.Modules.pullback g).obj M) n).hom ≫
          Tensor.Bifunctor.tensorModuleMap (TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullbackComp f g).hom.app L) n)
            (TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullbackComp f g).hom.app M) n) := by
      rw [Functor.map_comp, Category.assoc]
    _ = (Scheme.Modules.pullbackComp f g).hom.app (TensorPower.PowerSheaf.tensorPowerModule (Tensor.ProductSheaf.tensorModule L M) n) ≫
        (TensorPower.ProductPullbacks.tensorPowerOfTensorPullbackIso (f ≫ g) L M n).hom ≫
        (TensorPower.FrameComparison.tensorPowerFrameComparisonIso
          (Ample.LineBundles.pullbackSection f e ≫ (Scheme.Modules.pullbackComp f g).hom.app L)
          (Ample.LineBundles.pullbackSection f t ≫ (Scheme.Modules.pullbackComp f g).hom.app M) n).hom := by
      rw [TensorPowerComparison.localTensorPowerComparisonIso_spec]
      exact tensorPowerFrame_composite_transport f g e t n
    _ = _ := by rw [Category.assoc, TensorPowerComparison.localTensorPowerComparisonIso_spec]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorPowerComposition
