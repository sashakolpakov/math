import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TripleTensorPullbacks

/-! # Triple Tensor Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TripleTensorComposition

noncomputable section

/-! Triple tensor pullback comparisons commute with composition of open immersions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem leftTripleTensorPullbackIso_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (L M N : Z.Modules) :
    (Scheme.Modules.pullback f).map (TripleTensorPullbacks.leftTripleTensorPullbackIso g L M N).hom ≫
      (TripleTensorPullbacks.leftTripleTensorPullbackIso f ((Scheme.Modules.pullback g).obj L)
        ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)).hom ≫
      Tensor.Bifunctor.tensorModuleMap (Tensor.Bifunctor.tensorModuleMap ((Scheme.Modules.pullbackComp f g).hom.app L)
        ((Scheme.Modules.pullbackComp f g).hom.app M)) ((Scheme.Modules.pullbackComp f g).hom.app N) =
      (Scheme.Modules.pullbackComp f g).hom.app (Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule L M) N) ≫
        (TripleTensorPullbacks.leftTripleTensorPullbackIso (f ≫ g) L M N).hom := by
  change (Scheme.Modules.pullback f).map
      (Tensor.PullbackComparison.tensorPullbackComparison g (Tensor.ProductSheaf.tensorModule L M) N ≫
        Tensor.Bifunctor.tensorModuleMap (Tensor.PullbackComparison.tensorPullbackComparison g L M) (𝟙 _)) ≫
    (Tensor.PullbackComparison.tensorPullbackComparison f
      (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback g).obj L) ((Scheme.Modules.pullback g).obj M))
      ((Scheme.Modules.pullback g).obj N) ≫
      Tensor.Bifunctor.tensorModuleMap (Tensor.PullbackComparison.tensorPullbackComparison f ((Scheme.Modules.pullback g).obj L)
        ((Scheme.Modules.pullback g).obj M)) (𝟙 _)) ≫ _ =
    _ ≫ (Tensor.PullbackComparison.tensorPullbackComparison (f ≫ g) (Tensor.ProductSheaf.tensorModule L M) N ≫
      Tensor.Bifunctor.tensorModuleMap (Tensor.PullbackComparison.tensorPullbackComparison (f ≫ g) L M) (𝟙 _))
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback f).map
    (Tensor.Bifunctor.tensorModuleMap (Tensor.PullbackComparison.tensorPullbackComparison g L M) (𝟙 _))), Tensor.PullbackComparison.tensorPullbackComparison_natural]
  simp only [Category.assoc]
  rw [Tensor.Bifunctor.tensorModuleMap_comp, Tensor.Bifunctor.tensorModuleMap_comp]
  simp only [Category.id_comp]
  rw [Tensor.PullbackComposition.tensorPullbackComparison_comp]
  have hN : (Scheme.Modules.pullback f).map (𝟙 ((Scheme.Modules.pullback g).obj N)) ≫
      (Scheme.Modules.pullbackComp f g).hom.app N = (Scheme.Modules.pullbackComp f g).hom.app N :=
    (congrArg (fun a => a ≫ (Scheme.Modules.pullbackComp f g).hom.app N)
      ((Scheme.Modules.pullback f).map_id ((Scheme.Modules.pullback g).obj N))).trans (Category.id_comp _)
  rw [hN]
  have h : Tensor.Bifunctor.tensorModuleMap
      ((Scheme.Modules.pullbackComp f g).hom.app (Tensor.ProductSheaf.tensorModule L M) ≫
        Tensor.PullbackComparison.tensorPullbackComparison (f ≫ g) L M) ((Scheme.Modules.pullbackComp f g).hom.app N) =
      Tensor.Bifunctor.tensorModuleMap ((Scheme.Modules.pullbackComp f g).hom.app (Tensor.ProductSheaf.tensorModule L M))
        ((Scheme.Modules.pullbackComp f g).hom.app N) ≫
      Tensor.Bifunctor.tensorModuleMap (Tensor.PullbackComparison.tensorPullbackComparison (f ≫ g) L M) (𝟙 _) := by
    rw [Tensor.Bifunctor.tensorModuleMap_comp, Category.comp_id]
  rw [h]
  rw [← Category.assoc (Tensor.PullbackComparison.tensorPullbackComparison f
    ((Scheme.Modules.pullback g).obj (Tensor.ProductSheaf.tensorModule L M)) ((Scheme.Modules.pullback g).obj N)),
    ← Category.assoc ((Scheme.Modules.pullback f).map (Tensor.PullbackComparison.tensorPullbackComparison g (Tensor.ProductSheaf.tensorModule L M) N)),
    Tensor.PullbackComposition.tensorPullbackComparison_comp]
  exact Category.assoc _ _ _

theorem rightTripleTensorPullbackIso_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (L M N : Z.Modules) :
    (Scheme.Modules.pullback f).map (TripleTensorPullbacks.rightTripleTensorPullbackIso g L M N).hom ≫
      (TripleTensorPullbacks.rightTripleTensorPullbackIso f ((Scheme.Modules.pullback g).obj L)
        ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)).hom ≫
      Tensor.Bifunctor.tensorModuleMap ((Scheme.Modules.pullbackComp f g).hom.app L)
        (Tensor.Bifunctor.tensorModuleMap ((Scheme.Modules.pullbackComp f g).hom.app M)
          ((Scheme.Modules.pullbackComp f g).hom.app N)) =
      (Scheme.Modules.pullbackComp f g).hom.app (Tensor.ProductSheaf.tensorModule L (Tensor.ProductSheaf.tensorModule M N)) ≫
        (TripleTensorPullbacks.rightTripleTensorPullbackIso (f ≫ g) L M N).hom := by
  change (Scheme.Modules.pullback f).map
      (Tensor.PullbackComparison.tensorPullbackComparison g L (Tensor.ProductSheaf.tensorModule M N) ≫
        Tensor.Bifunctor.tensorModuleMap (𝟙 _) (Tensor.PullbackComparison.tensorPullbackComparison g M N)) ≫
    (Tensor.PullbackComparison.tensorPullbackComparison f ((Scheme.Modules.pullback g).obj L)
      (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)) ≫
      Tensor.Bifunctor.tensorModuleMap (𝟙 _) (Tensor.PullbackComparison.tensorPullbackComparison f ((Scheme.Modules.pullback g).obj M)
        ((Scheme.Modules.pullback g).obj N))) ≫ _ =
    _ ≫ (Tensor.PullbackComparison.tensorPullbackComparison (f ≫ g) L (Tensor.ProductSheaf.tensorModule M N) ≫
      Tensor.Bifunctor.tensorModuleMap (𝟙 _) (Tensor.PullbackComparison.tensorPullbackComparison (f ≫ g) M N))
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback f).map
    (Tensor.Bifunctor.tensorModuleMap (𝟙 _) (Tensor.PullbackComparison.tensorPullbackComparison g M N))), Tensor.PullbackComparison.tensorPullbackComparison_natural]
  simp only [Category.assoc]
  rw [Tensor.Bifunctor.tensorModuleMap_comp, Tensor.Bifunctor.tensorModuleMap_comp]
  simp only [Category.id_comp]
  rw [Tensor.PullbackComposition.tensorPullbackComparison_comp]
  have hL : (Scheme.Modules.pullback f).map (𝟙 ((Scheme.Modules.pullback g).obj L)) ≫
      (Scheme.Modules.pullbackComp f g).hom.app L = (Scheme.Modules.pullbackComp f g).hom.app L :=
    (congrArg (fun a => a ≫ (Scheme.Modules.pullbackComp f g).hom.app L)
      ((Scheme.Modules.pullback f).map_id ((Scheme.Modules.pullback g).obj L))).trans (Category.id_comp _)
  rw [hL]
  have h : Tensor.Bifunctor.tensorModuleMap ((Scheme.Modules.pullbackComp f g).hom.app L)
      ((Scheme.Modules.pullbackComp f g).hom.app (Tensor.ProductSheaf.tensorModule M N) ≫
        Tensor.PullbackComparison.tensorPullbackComparison (f ≫ g) M N) =
      Tensor.Bifunctor.tensorModuleMap ((Scheme.Modules.pullbackComp f g).hom.app L)
        ((Scheme.Modules.pullbackComp f g).hom.app (Tensor.ProductSheaf.tensorModule M N)) ≫
      Tensor.Bifunctor.tensorModuleMap (𝟙 _) (Tensor.PullbackComparison.tensorPullbackComparison (f ≫ g) M N) := by
    rw [Tensor.Bifunctor.tensorModuleMap_comp, Category.comp_id]
  rw [h]
  rw [← Category.assoc (Tensor.PullbackComparison.tensorPullbackComparison f
    ((Scheme.Modules.pullback g).obj L) ((Scheme.Modules.pullback g).obj (Tensor.ProductSheaf.tensorModule M N))),
    ← Category.assoc ((Scheme.Modules.pullback f).map (Tensor.PullbackComparison.tensorPullbackComparison g L (Tensor.ProductSheaf.tensorModule M N))),
    Tensor.PullbackComposition.tensorPullbackComparison_comp]
  exact Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TripleTensorComposition
