import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.RetractionLevel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.RetractionIsoIdentification
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.VaryingDualReduction
import Mathlib.Analysis.Complex.Basic

/-! # Product Level -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductLevel

noncomputable section

/-! The actual normalized product over complex dual numbers preserves
its original ordered full level, by the general surjective-retraction theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {g N : ℕ} [NeZero N] {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of (DualNumber ℂ))))
    (e : A.abelian.scheme ≅ ((A.abelian.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ)).scheme)
    [IsMonHom e.hom]

theorem normalizedDualProduct_level (he : OpenProductData.NormalizesDualProductFiber ℂ e) :
    A.level.transport (A := A.abelian)
      (B := (A.abelian.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ)) e =
      (A.level.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ) := by
  have h : OpenProductData.NormalizesProductFiber (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ)) (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ))
      (Pullback.RetractionIso.pullbackRetractionIso (Smooth.AffineDualProduct.dualBaseProjection ℂ) (Smooth.AffineDualProduct.dualBaseReduction ℂ) (Normalized.SmoothAffineDualProduct.dualBaseReduction_projection ℂ)) e := by
    rw [← Dual.RetractionIsoIdentification.dualProductSpecialFiberIso_eq_retraction]
    exact he
  exact Normalized.RetractionLevel.normalizedRetraction_level (Smooth.AffineDualProduct.dualBaseProjection ℂ) (Smooth.AffineDualProduct.dualBaseReduction ℂ) (Normalized.SmoothAffineDualProduct.dualBaseReduction_projection ℂ) A e h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductLevel
