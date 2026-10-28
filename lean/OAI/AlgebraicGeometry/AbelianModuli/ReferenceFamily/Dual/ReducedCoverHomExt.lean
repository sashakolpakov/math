import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.LiteralAffineCover
import Mathlib.AlgebraicGeometry.Gluing

/-! # Reduced Cover Hom Ext -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReducedCoverHomExt

noncomputable section

/-! The actual reduced affine cover detects equality of morphisms
over the coefficient field, independently of any product comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k)))) (U : X.left.AffineOpenCover)

theorem dualReducedLiteralCover_hom_ext {Y : Over (Spec (.of k))}
    (f g : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X ⟶ Y)
    (h : ∀ i : U.I₀,
      (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map
          (OpenChart.dualFamilyOpenInclusion k X (ChartGauge.dualFamilyChartAffineOpen k X U i).1) ≫ f =
        (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map
          (OpenChart.dualFamilyOpenInclusion k X (ChartGauge.dualFamilyChartAffineOpen k X U i).1) ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply (LiteralAffineCover.dualFamilyReducedAffineCover k X U).hom_ext
  intro i
  exact congrArg Over.Hom.left (h i)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReducedCoverHomExt
