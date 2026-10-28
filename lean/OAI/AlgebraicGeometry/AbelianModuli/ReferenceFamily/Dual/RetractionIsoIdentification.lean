import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.RetractionIso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.SmoothAffineDualProduct

/-! # Retraction Iso Identification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.RetractionIsoIdentification

noncomputable section

/-! The original dual-number fiber comparison is the canonical
comparison for its actual retraction of base schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem dualProductSpecialFiberIso_eq_retraction (k : Type) [CommRing k] :
    Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k = Pullback.RetractionIso.pullbackRetractionIso
      (Smooth.AffineDualProduct.dualBaseProjection k) (Smooth.AffineDualProduct.dualBaseReduction k) (Normalized.SmoothAffineDualProduct.dualBaseReduction_projection k) := by
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.RetractionIsoIdentification
