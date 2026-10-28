import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps

/-! # Pullback Map -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap

noncomputable section

/-!
# The canonical tensor comparison for arbitrary geometric pullback
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Direct image of a bilinear map respects precomposition of both arguments. -/
theorem pushforward_precomp {M M' N N' P : X.Modules} (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P)
    (a : M' ⟶ M) (b : N' ⟶ N) :
    (β.precomp a b).pushforward f = (β.pushforward f).precomp
      ((Scheme.Modules.pushforward f).map a) ((Scheme.Modules.pushforward f).map b) := by
  ext U x y
  rfl

/-- The two actual adjunction units turn a pulled-back bilinear map into a bilinear map on the base. -/
def bilinearAdjoint (M N : Y.Modules) {P : X.Modules}
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) P) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N ((Scheme.Modules.pushforward f).obj P) :=
  (β.pushforward f).precomp ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N)

/-- The bilinear adjunction construction is natural in its output. -/
theorem bilinearAdjoint_postcomp (M N : Y.Modules) {P Q : X.Modules}
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) P)
    (t : P ⟶ Q) :
    bilinearAdjoint f M N (β.postcomp t) =
      (bilinearAdjoint f M N β).postcomp ((Scheme.Modules.pushforward f).map t) := by
  unfold bilinearAdjoint
  rw [AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.pushforward_postcomp, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_postcomp]

/-- The bilinear adjunction construction is natural in both input sheaves. -/
theorem bilinearAdjoint_precomp {M M' N N' : Y.Modules} {P : X.Modules}
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj M') ((Scheme.Modules.pullback f).obj N') P)
    (a : M ⟶ M') (b : N ⟶ N') :
    bilinearAdjoint f M N (β.precomp ((Scheme.Modules.pullback f).map a)
      ((Scheme.Modules.pullback f).map b)) = (bilinearAdjoint f M' N' β).precomp a b := by
  unfold bilinearAdjoint
  rw [pushforward_precomp, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_comp, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_comp]
  exact congrArg₂ (fun x y => (β.pushforward f).precomp x y)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a).symm
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality b).symm

/-- The canonical map from pullback of a tensor sheaf to the tensor of the actual pullbacks. -/
def pullbackMap (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ⟶
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    ((AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).symm (bilinearAdjoint f M N
      (SheafMaps.tensorBilinear ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N))))

/-- Its adjoint has exactly the bilinear formula supplied by the two pullback units. -/
theorem pullbackMap_characterization (M N : Y.Modules) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _ ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (pullbackMap f M N)) =
    bilinearAdjoint f M N (SheafMaps.tensorBilinear ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N)) := by
  unfold pullbackMap
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Postcomposition of the canonical comparison gives the expected adjoint bilinear map. -/
theorem pullbackMap_postcomp (M N : Y.Modules) {P : X.Modules}
    (t : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) ⟶ P) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _ ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (pullbackMap f M N ≫ t)) =
    bilinearAdjoint f M N (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) P t) := by
  rw [Adjunction.homEquiv_naturality_right, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, pullbackMap_characterization,
    ← bilinearAdjoint_postcomp, SheafMaps.tensorBilinear_postcomp]

/-- The canonical tensor comparison is natural in both original sheaves. -/
theorem pullbackMap_naturality {M M' N N' : Y.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    (Scheme.Modules.pullback f).map (SheafMaps.tensorMap a b) ≫ pullbackMap f M' N' =
      pullbackMap f M N ≫ SheafMaps.tensorMap ((Scheme.Modules.pullback f).map a) ((Scheme.Modules.pullback f).map b) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).injective
  rw [Adjunction.homEquiv_naturality_left, SheafMaps.tensorMap_precomp, pullbackMap_characterization,
    pullbackMap_postcomp, SheafMaps.tensorMap_bilinear, bilinearAdjoint_precomp]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap
