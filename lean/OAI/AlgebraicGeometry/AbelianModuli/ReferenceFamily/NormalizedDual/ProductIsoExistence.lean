import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductIsoExistence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductData
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.MapComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.Witness

/-! # Product Iso Existence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductIsoExistence

noncomputable section

/-! The actual isomorphism witness retains the canonical normalization
as well as the exact original map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] OpenProductData.NormalizesProductFiber
attribute [local irreducible] Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

theorem exists_normalized_dualProductIso_of_openCharts (k : Type) [Field k]
    (X : Over (Spec (.of (DualNumber k))))
    (f : X ⟶ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X))
    (hf : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f ≫
      (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k).hom.app ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X) = 𝟙 _)
    (U : X.left.OpenCover) (hU : ∀ i : U.I₀, IsOpenImmersion (U.f i ≫ f.left)) :
    ∃ e : X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X),
      OpenProductData.NormalizesDualProductFiber k e ∧ e.hom = f :=
  NormalizedProduct.Witness.normalizedProductIsoWitness_of_map (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k))
    (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)) (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k) f hf
    (Dual.ProductIsoExistence.exists_dualProductIso_of_normalized_openCharts k X f hf U hU)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductIsoExistence
