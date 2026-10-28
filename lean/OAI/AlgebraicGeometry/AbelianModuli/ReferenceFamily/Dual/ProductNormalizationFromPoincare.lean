import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProductNormalizationFromPoincare
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.RetractionIsoIdentification
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductData

/-! # Product Normalization From Poincare -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductNormalizationFromPoincare

noncomputable section

/-! Poincare compatibility forces the dual comparison to induce the
identity on the actual special fiber whenever the abelian comparison does.
The reference comparison is the proved polarized pullback retraction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {k : Type} [CommRing k] {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of (DualNumber k))))
    (e : A.abelian.scheme ≅ ((A.abelian.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).pullback (Smooth.AffineDualProduct.dualBaseProjection k)).scheme)
    (d : A.dual.abelian.scheme ≅ ((A.dual.abelian.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).pullback (Smooth.AffineDualProduct.dualBaseProjection k)).scheme)

theorem dualProduct_normalized_of_poincare (he : NormalizedDual.OpenProductData.NormalizesDualProductFiber k e)
    (hp : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d.hom ⊗ₘ e.hom).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf ((A.dual.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).pullback (Smooth.AffineDualProduct.dualBaseProjection k)).poincare) =
        HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare) : NormalizedDual.OpenProductData.NormalizesDualProductFiber k d := by
  have h : NormalizedDual.OpenProductData.NormalizesProductFiber (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)) (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k))
      (Pullback.RetractionIso.pullbackRetractionIso (Smooth.AffineDualProduct.dualBaseProjection k) (Smooth.AffineDualProduct.dualBaseReduction k) (Normalized.SmoothAffineDualProduct.dualBaseReduction_projection k)) e := by
    rw [← RetractionIsoIdentification.dualProductSpecialFiberIso_eq_retraction]
    exact he
  have hd := ProductNormalizationFromPoincare.retractionProduct_normalized_of_poincare (Smooth.AffineDualProduct.dualBaseProjection k) (Smooth.AffineDualProduct.dualBaseReduction k)
    (Normalized.SmoothAffineDualProduct.dualBaseReduction_projection k) A e d h hp
  rw [← RetractionIsoIdentification.dualProductSpecialFiberIso_eq_retraction] at hd
  exact hd

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductNormalizationFromPoincare
