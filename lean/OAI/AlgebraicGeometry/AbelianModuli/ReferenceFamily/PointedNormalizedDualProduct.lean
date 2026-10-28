import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointedProductFiberNormalization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupDescentIs

/-! # Pointed Normalized Dual Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointedNormalizedDualProduct

noncomputable section

/-! An actual normalized product of a group scheme over dual numbers
can be chosen to preserve the original identity section as well. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (k : Type) [CommRing k] (X : Over (Spec (.of (DualNumber k)))) [GrpObj X]

theorem exists_pointed_normalizedDualProduct
    (e : X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X))
    (he : NormalizedDual.OpenProductData.NormalizesDualProductFiber k e) :
    ∃ e' : X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X),
      NormalizedDual.OpenProductData.NormalizesDualProductFiber k e' ∧
        η[X] ≫ e'.hom = η[(Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X)] :=
  PointedProductFiberNormalization.exists_pointed_normalizedProduct (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)) (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k))
    (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k) X e he

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointedNormalizedDualProduct
