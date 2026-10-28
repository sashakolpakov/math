import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.DualProductComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductLevel

/-! # Polarized Level Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.PolarizedLevelProduct

noncomputable section

/-! A normalized abelian group product upgrades to an actual HilbertConstruction
polarized full-level isomorphism, with the represented dual, Poincare
class, polarization morphism, and every ordered test-scheme level point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {g N : ℕ} [NeZero N] {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of (DualNumber ℂ))))
    (e : A.abelian.scheme ≅ ((A.abelian.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ)).scheme)
    [heGroup : IsMonHom e.hom]

def normalizedPolarizedLevelProduct (he : NormalizedDual.OpenProductData.NormalizesDualProductFiber ℂ e) :
    HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A ((A.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ)) where
  abelian := e
  dual := Abelian.DualProductComparison.abelianDualProductComparison A.abelian A.dual e
  abelianGroup := heGroup
  dualGroup := Polarized.DualProductComparison.polarizedDualProductComparison_isMonHom A e he
  polarization := Polarized.DualProductComparison.normalizedDualProduct_polarization A e he
  poincare := Polarized.DualProductPoincare.polarizedDualProductComparison_poincare A e
  level T c := by
    have h := congrArg (fun β : ((A.abelian.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ)).FullLevel N =>
      (β.hom.app (.op T) c).val) (NormalizedDual.ProductLevel.normalizedDualProduct_level A e he)
    exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.PolarizedLevelProduct
