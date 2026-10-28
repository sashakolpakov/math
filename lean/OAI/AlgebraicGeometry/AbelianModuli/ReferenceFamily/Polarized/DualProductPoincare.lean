import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.DualProductComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedDualPoincareCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.FieldProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange
import Mathlib.RingTheory.DualNumber

/-! # Dual Product Poincare -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.DualProductPoincare

noncomputable section

/-! The canonical comparison for a polarized abelian product preserves
the original Poincare class. Its projective presentation is constructed
from the polarized special fiber and ordinary base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of (DualNumber ℂ))))
    (e : A.abelian.scheme ≅ ((A.abelian.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ)).scheme)
    [IsMonHom e.hom]

theorem polarizedDualProductComparison_poincare :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Abelian.DualProductComparison.abelianDualProductComparison A.abelian A.dual e).hom ⊗ₘ e.hom).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf ((A.dual.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ)).poincare) =
        HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare := by
  have : IsLocallyNoetherian (Spec (.of (DualNumber ℂ))) := inferInstance
  exact RepresentedDualPoincareCompatibility.representedDualComparison_poincare A.dual
    ((A.dual.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ)) e
    ((A.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).projectivePresentation_overField.baseChange (Smooth.AffineDualProduct.dualBaseProjection ℂ))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.DualProductPoincare
