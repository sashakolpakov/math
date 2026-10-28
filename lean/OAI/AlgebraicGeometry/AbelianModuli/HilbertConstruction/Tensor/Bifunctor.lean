import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.BilinearRestriction

/-! # Bifunctor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Bifunctor

noncomputable section

/-! Functorial maps on the actual tensor product of module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def tensorBilinear (M N : X.Modules) : Bilinear.Sheaves.SheafBilinearMap M N (ProductSheaf.tensorModule M N) :=
  Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _ (𝟙 _)

theorem tensorBilinear_postcomp {M N P : X.Modules} (f : ProductSheaf.tensorModule M N ⟶ P) :
    (tensorBilinear M N).postcomp f = Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P f := by
  exact (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp (𝟙 _) f).symm.trans
    (congrArg (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P) (Category.id_comp f))

def tensorModuleMap {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    ProductSheaf.tensorModule M N ⟶ ProductSheaf.tensorModule M' N' :=
  (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).symm ((tensorBilinear M' N').precomp f g)

theorem tensorModuleMap_spec {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    (tensorBilinear M N).postcomp (tensorModuleMap f g) =
      (tensorBilinear M' N').precomp f g :=
  (tensorBilinear_postcomp _).trans (Equiv.apply_symm_apply _ _)

theorem tensorModuleMap_id (M N : X.Modules) :
    tensorModuleMap (𝟙 M) (𝟙 N) = 𝟙 (ProductSheaf.tensorModule M N) := by
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).injective
  exact (Equiv.apply_symm_apply _ _).trans (Bilinear.Sheaves.SheafBilinearMap.precomp_id _)

theorem tensorModuleMap_comp {M M' M'' N N' N'' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') (f' : M' ⟶ M'') (g' : N' ⟶ N'') :
    tensorModuleMap f g ≫ tensorModuleMap f' g' = tensorModuleMap (f ≫ f') (g ≫ g') := by
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).injective
  rw [← tensorBilinear_postcomp, Bilinear.Sheaves.SheafBilinearMap.postcomp_comp, tensorModuleMap_spec,
    ← Bilinear.Sheaves.SheafBilinearMap.precomp_postcomp, tensorModuleMap_spec,
    Bilinear.Sheaves.SheafBilinearMap.precomp_comp, ← tensorModuleMap_spec, tensorBilinear_postcomp]

def tensorModuleMapIso {M M' N N' : X.Modules} (e : M ≅ M') (f : N ≅ N') :
    ProductSheaf.tensorModule M N ≅ ProductSheaf.tensorModule M' N' where
  hom := tensorModuleMap e.hom f.hom
  inv := tensorModuleMap e.inv f.inv
  hom_inv_id := by rw [tensorModuleMap_comp, e.hom_inv_id, f.hom_inv_id, tensorModuleMap_id]
  inv_hom_id := by rw [tensorModuleMap_comp, e.inv_hom_id, f.inv_hom_id, tensorModuleMap_id]

instance tensorModuleMap_isIso {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N')
    [IsIso f] [IsIso g] : IsIso (tensorModuleMap f g) :=
  (tensorModuleMapIso (asIso f) (asIso g)).isIso_hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Bifunctor
