import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.BilinearRestriction

/-! # Sheaf Maps -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps

noncomputable section

/-!
# Canonical maps of actual tensor sheaves

This uses the existing sectionwise tensor product and its proved bilinear universal property.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

/-- The universal bilinear map into the actual tensor sheaf. -/
def tensorBilinear (M N : X.Modules) : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) :=
  AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) (𝟙 _)

/-- Composing the universal bilinear map gives the bilinear formula for a tensor morphism. -/
theorem tensorBilinear_postcomp {M N P : X.Modules} (a : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ⟶ P) :
    (tensorBilinear M N).postcomp a = AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P a := by
  unfold tensorBilinear
  rw [← AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp]
  exact congrArg (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P) (Category.id_comp a)

/-- Two sheaf maps induce the canonical map of their tensor sheaves. -/
def tensorMap {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ⟶ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M' N' :=
  (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M' N')).symm ((tensorBilinear M' N').precomp a b)

/-- The induced tensor map has precisely the prescribed bilinear formula. -/
theorem tensorMap_bilinear {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M' N') (tensorMap a b) = (tensorBilinear M' N').precomp a b :=
  (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M' N')).apply_symm_apply _

/-- The bilinear universal property is natural in both tensor inputs. -/
theorem tensorMap_precomp {M M' N N' P : X.Modules} (a : M ⟶ M') (b : N ⟶ N')
    (t : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M' N' ⟶ P) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P (tensorMap a b ≫ t) = (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M' N' P t).precomp a b := by
  rw [AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, tensorMap_bilinear, ← AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_postcomp, tensorBilinear_postcomp]

/-- The canonical tensor operation preserves identity morphisms. -/
theorem tensorMap_id (M N : X.Modules) : tensorMap (𝟙 M) (𝟙 N) = 𝟙 (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) := by
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)).injective
  rw [tensorMap_bilinear, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_id]
  rfl

/-- The canonical tensor operation preserves composition in both factors. -/
theorem tensorMap_comp {M M' M'' N N' N'' : X.Modules}
    (a : M ⟶ M') (b : N ⟶ N') (a' : M' ⟶ M'') (b' : N' ⟶ N'') :
    tensorMap a b ≫ tensorMap a' b' = tensorMap (a ≫ a') (b ≫ b') := by
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M'' N'')).injective
  rw [tensorMap_precomp, tensorMap_bilinear, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_comp, tensorMap_bilinear]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps
