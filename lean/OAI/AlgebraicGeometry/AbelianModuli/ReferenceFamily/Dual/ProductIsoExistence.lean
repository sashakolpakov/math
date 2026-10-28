import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.IsoReduced
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductReductionIsomorphism

/-! # Product Iso Existence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductIsoExistence

noncomputable section

/-! A normalized actual map with open local charts has an actual
isomorphism witness over the base whose map is exactly the original one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local irreducible] Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

theorem exists_dualProductIso_of_normalized_openCharts (k : Type) [Field k]
    (X : Over (Spec (.of (DualNumber k))))
    (f : X ⟶ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X))
    (hf : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f ≫
      (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k).hom.app ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X) = 𝟙 _)
    (U : X.left.OpenCover) (hU : ∀ i : U.I₀, IsOpenImmersion (U.f i ≫ f.left)) :
    ∃ e : X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X),
      e.hom = f := by
  have hred := ProductReductionIsomorphism.dualProductMap_reduction_isIso k X f hf
  exact ⟨IsoReduced.dualProductIsoWithReducedIso k X f hred U hU, IsoReduced.dualProductIsoWithReducedIso_hom k X f hred U hU⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductIsoExistence
