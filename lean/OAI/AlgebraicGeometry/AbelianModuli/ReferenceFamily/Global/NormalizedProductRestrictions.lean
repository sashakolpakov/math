import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductRestriction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.OpenMapLaws
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartRestrictionSquares

/-! # Normalized Product Restrictions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.NormalizedProductRestrictions

noncomputable section

/-! A normalized global product isomorphism restricts canonically to
actual open subfamilies, with compatible further restrictions. These
restrictions will recover a primitive of the constructed transition cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local irreducible] Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k))))
    (e : X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X))
    (he : NormalizedDual.OpenProductData.NormalizesDualProductFiber k e)

def globalNormalizedProductOnOpen (V : X.left.Opens) := by
  have := Dual.OpenChart.dualFamilyOpenInclusion_open k X V
  exact NormalizedDual.OpenProductRestriction.restrictNormalizedDualProduct k (Dual.OpenChart.dualFamilyOpenInclusion k X V) e he

theorem globalNormalizedProductOnOpen_restriction {V W : X.left.Opens} (h : V ≤ W) :
    (globalNormalizedProductOnOpen k X e he V).iso.hom ≫
        (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).map
          ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (Dual.OpenChart.dualFamilyOpenMap k X h)) =
      Dual.OpenChart.dualFamilyOpenMap k X h ≫ (globalNormalizedProductOnOpen k X e he W).iso.hom := by
  let P := Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k) ⋙ Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)
  have := Dual.OpenChart.dualFamilyOpenInclusion_open k X W
  have : Mono (Dual.OpenChart.dualFamilyOpenInclusion k X W) := Over.mono_of_mono_left (Dual.OpenChart.dualFamilyOpenInclusion k X W)
  have : Mono (P.map (Dual.OpenChart.dualFamilyOpenInclusion k X W)) := inferInstance
  exact Product.ChartRestrictionSquares.productChart_restriction_square P (Dual.OpenChart.dualFamilyOpenMap k X h)
    (Dual.OpenChart.dualFamilyOpenInclusion k X W) (Dual.OpenChart.dualFamilyOpenInclusion k X V)
    (Dual.OpenChart.dualFamilyOpenMap_inclusion k X h) e
    (globalNormalizedProductOnOpen k X e he V).iso (globalNormalizedProductOnOpen k X e he W).iso
    (globalNormalizedProductOnOpen k X e he V).commutes (globalNormalizedProductOnOpen k X e he W).commutes

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.NormalizedProductRestrictions
