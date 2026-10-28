import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorAssociator

/-! # Tensor Associator Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorAssociatorComposition

noncomputable section

/-! Local associators agree after refinement by another open immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsOpenImmersion f] [IsOpenImmersion g] {L M N : Z.Modules}
variable (e : Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback g).obj L)
variable (t : Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback g).obj M)
variable (r : Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback g).obj N)
variable [IsIso e] [IsIso t] [IsIso r]

theorem tensorAssociatorFrame_composite_transport :
    (Scheme.Modules.pullback f).map
      ((TripleTensorPullbacks.leftTripleTensorPullbackIso g L M N).hom ≫ (Tensor.AssociatorFrames.tensorAssociatorFrameIso e t r).hom) ≫
      (TripleTensorPullbacks.rightTripleTensorPullbackIso f ((Scheme.Modules.pullback g).obj L)
        ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)).hom ≫
      Tensor.Bifunctor.tensorModuleMap ((Scheme.Modules.pullbackComp f g).hom.app L)
        (Tensor.Bifunctor.tensorModuleMap ((Scheme.Modules.pullbackComp f g).hom.app M)
          ((Scheme.Modules.pullbackComp f g).hom.app N)) =
      (Scheme.Modules.pullbackComp f g).hom.app (Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule L M) N) ≫
        (TripleTensorPullbacks.leftTripleTensorPullbackIso (f ≫ g) L M N).hom ≫
        (Tensor.AssociatorFrames.tensorAssociatorFrameIso
          (Ample.LineBundles.pullbackSection f e ≫ (Scheme.Modules.pullbackComp f g).hom.app L)
          (Ample.LineBundles.pullbackSection f t ≫ (Scheme.Modules.pullbackComp f g).hom.app M)
          (Ample.LineBundles.pullbackSection f r ≫ (Scheme.Modules.pullbackComp f g).hom.app N)).hom := by
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback f).map (Tensor.AssociatorFrames.tensorAssociatorFrameIso e t r).hom),
    TripleTensorPullbacks.tensorAssociatorFrameIso_pullback]
  simp only [Category.assoc]
  rw [← Tensor.AssociatorFrames.tensorAssociatorFrameIso_natural]
  rw [← Category.assoc (TripleTensorPullbacks.leftTripleTensorPullbackIso f ((Scheme.Modules.pullback g).obj L)
    ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)).hom,
    ← Category.assoc ((Scheme.Modules.pullback f).map (TripleTensorPullbacks.leftTripleTensorPullbackIso g L M N).hom),
    TripleTensorComposition.leftTripleTensorPullbackIso_comp]
  exact Category.assoc _ _ _

theorem localTensorAssociatorIso_comp :
    (Scheme.Modules.pullback f).map (TensorAssociator.localTensorAssociatorIso g e t r).hom ≫
      (Scheme.Modules.pullbackComp f g).hom.app (Tensor.ProductSheaf.tensorModule L (Tensor.ProductSheaf.tensorModule M N)) =
      (Scheme.Modules.pullbackComp f g).hom.app (Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule L M) N) ≫
        (TensorAssociator.localTensorAssociatorIso (f ≫ g)
          (Ample.LineBundles.pullbackSection f e ≫ (Scheme.Modules.pullbackComp f g).hom.app L)
          (Ample.LineBundles.pullbackSection f t ≫ (Scheme.Modules.pullbackComp f g).hom.app M)
          (Ample.LineBundles.pullbackSection f r ≫ (Scheme.Modules.pullbackComp f g).hom.app N)).hom := by
  apply (cancel_mono (TripleTensorPullbacks.rightTripleTensorPullbackIso (f ≫ g) L M N).hom).mp
  calc
    _ = (Scheme.Modules.pullback f).map (TensorAssociator.localTensorAssociatorIso g e t r).hom ≫
        ((Scheme.Modules.pullback f).map (TripleTensorPullbacks.rightTripleTensorPullbackIso g L M N).hom ≫
          (TripleTensorPullbacks.rightTripleTensorPullbackIso f ((Scheme.Modules.pullback g).obj L)
            ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)).hom ≫
          Tensor.Bifunctor.tensorModuleMap ((Scheme.Modules.pullbackComp f g).hom.app L)
            (Tensor.Bifunctor.tensorModuleMap ((Scheme.Modules.pullbackComp f g).hom.app M)
              ((Scheme.Modules.pullbackComp f g).hom.app N))) := by
      rw [Category.assoc, ← TripleTensorComposition.rightTripleTensorPullbackIso_comp]
    _ = (Scheme.Modules.pullback f).map
        ((TensorAssociator.localTensorAssociatorIso g e t r).hom ≫ (TripleTensorPullbacks.rightTripleTensorPullbackIso g L M N).hom) ≫
          (TripleTensorPullbacks.rightTripleTensorPullbackIso f ((Scheme.Modules.pullback g).obj L)
            ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)).hom ≫
          Tensor.Bifunctor.tensorModuleMap ((Scheme.Modules.pullbackComp f g).hom.app L)
            (Tensor.Bifunctor.tensorModuleMap ((Scheme.Modules.pullbackComp f g).hom.app M)
              ((Scheme.Modules.pullbackComp f g).hom.app N)) := by
      rw [Functor.map_comp, Category.assoc]
    _ = (Scheme.Modules.pullbackComp f g).hom.app (Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule L M) N) ≫
        (TripleTensorPullbacks.leftTripleTensorPullbackIso (f ≫ g) L M N).hom ≫
        (Tensor.AssociatorFrames.tensorAssociatorFrameIso
          (Ample.LineBundles.pullbackSection f e ≫ (Scheme.Modules.pullbackComp f g).hom.app L)
          (Ample.LineBundles.pullbackSection f t ≫ (Scheme.Modules.pullbackComp f g).hom.app M)
          (Ample.LineBundles.pullbackSection f r ≫ (Scheme.Modules.pullbackComp f g).hom.app N)).hom := by
      rw [TensorAssociator.localTensorAssociatorIso_spec]
      exact tensorAssociatorFrame_composite_transport f g e t r
    _ = _ := by rw [Category.assoc, TensorAssociator.localTensorAssociatorIso_spec]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorAssociatorComposition
