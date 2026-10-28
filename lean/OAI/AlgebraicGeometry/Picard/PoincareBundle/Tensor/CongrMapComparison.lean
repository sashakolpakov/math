import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps
import OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorFunctors

/-! # Congr Map Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CongrMapComparison

noncomputable section

/-! The native tensor isomorphism and the bilinear-universal tensor map are the same sheaf map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {M M' N N' : X.Modules}

theorem tensorModuleMap_eq (a : M ⟶ M') (b : N ⟶ N') :
    Homomorphisms.TensorFunctors.Construction.tensorModuleMap a b = SheafMaps.tensorMap a b := by
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M' N')).injective
  have h := Homomorphisms.TensorFunctors.Construction.tensorModuleMap_homEquiv a b (𝟙 (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M' N'))
  rw [Category.comp_id] at h
  exact h.trans (SheafMaps.tensorMap_bilinear a b).symm

/-- The chosen actual tensor isomorphism has the canonical bilinear tensor map as its hom. -/
theorem congr_hom (e : M ≅ M') (f : N ≅ N') :
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr e f).hom = SheafMaps.tensorMap e.hom f.hom :=
  tensorModuleMap_eq e.hom f.hom

theorem congr_inv (e : M ≅ M') (f : N ≅ N') :
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr e f).inv = SheafMaps.tensorMap e.inv f.inv :=
  tensorModuleMap_eq e.inv f.inv

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CongrMapComparison
