import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductGroupIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.FamilyTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.RepresentingIsoPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.BaseChange

/-! # Dual Product Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.DualProductComparison

noncomputable section

/-! The represented Picard dual of an actual abelian product has a
canonical pointed comparison to the constant special-fiber dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of (DualNumber ℂ))))
    (D : HilbertConstruction.Dual.Data.DualAbelianData A)
    (e : A.scheme ≅ ((A.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ)).scheme)
    [IsMonHom e.hom]

def abelianDualProductComparison :
    D.abelian.scheme ≅ ((D.abelian.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ)).scheme :=
  (D.familyTransport e).uniqueUnderlyingIso
    ((D.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ))

theorem abelianDualProductComparison_pointed :
    η[D.abelian.scheme] ≫ (abelianDualProductComparison A D e).hom =
      η[((D.abelian.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ)).scheme] :=
  (D.familyTransport e).uniqueUnderlyingIso_preserves_unit
    ((D.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.DualProductComparison
