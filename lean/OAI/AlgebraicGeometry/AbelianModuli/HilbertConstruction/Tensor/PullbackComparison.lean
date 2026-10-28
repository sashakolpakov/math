import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Bifunctor

/-! # Pullback Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The canonical tensor comparison for arbitrary pullback of module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem Bilinear.Sheaves.SheafBilinearMap.pushforward_precomp {M M' N N' P : X.Modules}
    (β : Bilinear.Sheaves.SheafBilinearMap M N P) (f : X ⟶ Y) (a : M' ⟶ M) (b : N' ⟶ N) :
    (β.precomp a b).pushforward f = (β.pushforward f).precomp
      ((Scheme.Modules.pushforward f).map a) ((Scheme.Modules.pushforward f).map b) := by
  ext U x y
  rfl

theorem Tensor.PullbackComparison.tensorHomEquiv_precomp {M M' N N' P : Y.Modules}
    (a : M ⟶ M') (b : N ⟶ N') (h : Tensor.ProductSheaf.tensorModule M' N' ⟶ P) :
    Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P (Tensor.Bifunctor.tensorModuleMap a b ≫ h) =
      (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M' N' P h).precomp a b := by
  rw [← Tensor.Bifunctor.tensorBilinear_postcomp, Bilinear.Sheaves.SheafBilinearMap.postcomp_comp, Tensor.Bifunctor.tensorModuleMap_spec,
    ← Bilinear.Sheaves.SheafBilinearMap.precomp_postcomp, Tensor.Bifunctor.tensorBilinear_postcomp]

/-- A bilinear map on inverse images induces a bilinear map into its direct image. -/
def Tensor.PullbackComparison.bilinearPullbackUnit (f : X ⟶ Y) (M N : Y.Modules) (P : X.Modules)
    (β : Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) P) :
    Bilinear.Sheaves.SheafBilinearMap M N ((Scheme.Modules.pushforward f).obj P) :=
  (β.pushforward f).precomp ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N)

theorem Tensor.PullbackComparison.bilinearPullbackUnit_postcomp (f : X ⟶ Y) (M N : Y.Modules) {P Q : X.Modules}
    (β : Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) P) (h : P ⟶ Q) :
    Tensor.PullbackComparison.bilinearPullbackUnit f M N Q (β.postcomp h) =
      (Tensor.PullbackComparison.bilinearPullbackUnit f M N P β).postcomp ((Scheme.Modules.pushforward f).map h) := by
  exact (congrArg (fun γ => γ.precomp
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N))
      (β.pushforward_postcomp f h)).trans (Bilinear.Sheaves.SheafBilinearMap.precomp_postcomp _ _ _ _)

theorem Tensor.PullbackComparison.bilinearPullbackUnit_precomp (f : X ⟶ Y) {M M' N N' : Y.Modules} (P : X.Modules)
    (β : Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj M')
      ((Scheme.Modules.pullback f).obj N') P) (a : M ⟶ M') (b : N ⟶ N') :
    Tensor.PullbackComparison.bilinearPullbackUnit f M N P (β.precomp
      ((Scheme.Modules.pullback f).map a) ((Scheme.Modules.pullback f).map b)) =
      (Tensor.PullbackComparison.bilinearPullbackUnit f M' N' P β).precomp a b := by
  unfold Tensor.PullbackComparison.bilinearPullbackUnit
  rw [Bilinear.Sheaves.SheafBilinearMap.pushforward_precomp, Bilinear.Sheaves.SheafBilinearMap.precomp_comp,
    Bilinear.Sheaves.SheafBilinearMap.precomp_comp]
  exact congrArg₂ (fun c d => (β.pushforward f).precomp c d)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a).symm
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality b).symm

/-- The canonical map from the inverse image of a tensor product to the tensor of inverse images. -/
def Tensor.PullbackComparison.tensorPullbackComparison (f : X ⟶ Y) (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (Tensor.ProductSheaf.tensorModule M N) ⟶
      Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    ((Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).symm
      (Tensor.PullbackComparison.bilinearPullbackUnit f M N _
        (Tensor.Bifunctor.tensorBilinear ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N))))

theorem Tensor.PullbackComparison.tensorPullbackComparison_spec (f : X ⟶ Y) (M N : Y.Modules) :
    Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (Tensor.PullbackComparison.tensorPullbackComparison f M N)) =
      Tensor.PullbackComparison.bilinearPullbackUnit f M N _
        (Tensor.Bifunctor.tensorBilinear ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)) := by
  unfold Tensor.PullbackComparison.tensorPullbackComparison
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem Tensor.PullbackComparison.tensorPullbackComparison_natural (f : X ⟶ Y) {M M' N N' : Y.Modules}
    (a : M ⟶ M') (b : N ⟶ N') :
    (Scheme.Modules.pullback f).map (Tensor.Bifunctor.tensorModuleMap a b) ≫ Tensor.PullbackComparison.tensorPullbackComparison f M' N' =
      Tensor.PullbackComparison.tensorPullbackComparison f M N ≫ Tensor.Bifunctor.tensorModuleMap
        ((Scheme.Modules.pullback f).map a) ((Scheme.Modules.pullback f).map b) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).injective
  rw [(Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left,
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right,
    Tensor.PullbackComparison.tensorHomEquiv_precomp, Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp,
    Tensor.PullbackComparison.tensorPullbackComparison_spec, Tensor.PullbackComparison.tensorPullbackComparison_spec,
    ← Tensor.PullbackComparison.bilinearPullbackUnit_postcomp, Tensor.Bifunctor.tensorModuleMap_spec,
    Tensor.PullbackComparison.bilinearPullbackUnit_precomp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
