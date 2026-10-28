import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.ReductionIso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.SmoothAffineDualProduct

/-! # Product Reduction Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductReductionIsomorphism

/-! A map to the actual product that has the prescribed canonical
normalization induces an isomorphism on the actual special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local irreducible] Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

theorem dualProductMap_reduction_isIso (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k))))
    (f : X ⟶ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X))
    (hf : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f ≫
      (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k).hom.app ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X) = 𝟙 _) :
    IsIso ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f) :=
  NormalizedProduct.ReductionIso.normalizedProductMap_reduction_isIso (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k))
    (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)) (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k) (X := X) f hf

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductReductionIsomorphism
