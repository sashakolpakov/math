import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CongrMapComparison

/-! # Congr Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CongrComposition

noncomputable section

/-! Composition of the actual tensor isomorphisms in both factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CongrMapComparison

theorem trans {X : Scheme.{u}} {M M' M'' N N' N'' : X.Modules}
    (a : M ≅ M') (b : N ≅ N') (a' : M' ≅ M'') (b' : N' ≅ N'') :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a' b' = AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (a ≪≫ a') (b ≪≫ b') := by
  apply Iso.ext
  simp only [Iso.trans_hom, CongrMapComparison.congr_hom]
  exact SheafMaps.tensorMap_comp a.hom b.hom a'.hom b'.hom

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CongrComposition
