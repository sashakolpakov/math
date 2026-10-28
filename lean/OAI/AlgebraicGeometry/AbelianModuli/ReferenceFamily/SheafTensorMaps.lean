import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.Sheaves

/-! # Sheaf Tensor Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SheafTensorMaps

noncomputable section

/-! Maps and frame isomorphisms of the actual sheaf tensor product,
defined through its proved bilinear universal property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.Sheaves

variable {X : Scheme.{0}}

def tensorBilinear (M N : X.Modules) : HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) :=
  HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _ (𝟙 _)

theorem tensorBilinear_postcomp {M N P : X.Modules} (f : HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ⟶ P) :
    (tensorBilinear M N).postcomp f = HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P f :=
  (HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp (𝟙 _) f).symm.trans
    (congrArg (HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P) (Category.id_comp f))

def sheafTensorMap {M N P Q : X.Modules} (f : M ⟶ P) (h : N ⟶ Q) :
    HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ⟶ HilbertConstruction.Tensor.ProductSheaf.tensorModule P Q :=
  (HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).symm ((tensorBilinear P Q).precomp f h)

theorem sheafTensorMap_spec {M N P Q : X.Modules} (f : M ⟶ P) (h : N ⟶ Q) :
    (tensorBilinear M N).postcomp (sheafTensorMap f h) = (tensorBilinear P Q).precomp f h :=
  (tensorBilinear_postcomp _).trans ((HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).apply_symm_apply _)

theorem sheafTensorMap_id (M N : X.Modules) : sheafTensorMap (𝟙 M) (𝟙 N) = 𝟙 _ := by
  apply (HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).injective
  rw [← tensorBilinear_postcomp, sheafTensorMap_spec]
  exact (tensorBilinear M N).precomp_id

theorem sheafTensorMap_comp {M N P Q R T : X.Modules}
    (f : M ⟶ P) (h : N ⟶ Q) (a : P ⟶ R) (b : Q ⟶ T) :
    sheafTensorMap f h ≫ sheafTensorMap a b = sheafTensorMap (f ≫ a) (h ≫ b) := by
  apply (HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).injective
  rw [← tensorBilinear_postcomp, HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.postcomp_comp, sheafTensorMap_spec,
    ← HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_postcomp, sheafTensorMap_spec,
    ← tensorBilinear_postcomp, sheafTensorMap_spec]
  ext U x y
  rfl

def sheafTensorIso {M N P Q : X.Modules} (e : M ≅ P) (f : N ≅ Q) :
    HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ≅ HilbertConstruction.Tensor.ProductSheaf.tensorModule P Q where
  hom := sheafTensorMap e.hom f.hom
  inv := sheafTensorMap e.inv f.inv
  hom_inv_id := by rw [sheafTensorMap_comp, e.hom_inv_id, f.hom_inv_id, sheafTensorMap_id]
  inv_hom_id := by rw [sheafTensorMap_comp, e.inv_hom_id, f.inv_hom_id, sheafTensorMap_id]

theorem sheafTensorMap_apply {M N P Q : X.Modules} (f : M ⟶ P) (h : N ⟶ Q)
    (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)) :
    (sheafTensorMap f h).app U ((tensorBilinear M N).app U x y) =
      (tensorBilinear P Q).app U (f.app U x) (h.app U y) :=
  congrArg (fun β : HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N (HilbertConstruction.Tensor.ProductSheaf.tensorModule P Q) => β.app U x y)
    (sheafTensorMap_spec f h)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SheafTensorMaps
