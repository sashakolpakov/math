import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.NormalizedProductRestrictions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.CommonTransitions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenRestriction

/-! # Product Chart Differences -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.ProductChartDifferences

noncomputable section

/-! A given normalized global product supplies actual differences from
the selected affine charts. They fix the special fiber and commute with
restriction to smaller opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] NormalizedDual.OpenProductData.NormalizesProductFiber
attribute [local irreducible] Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso DualOpen.CommonTransitions.affineChartProductOnOpen

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k)))) [Smooth X.hom]
    (U : X.left.AffineOpenCover)
    (e : X ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).obj X))
    (he : NormalizedDual.OpenProductData.NormalizesDualProductFiber k e)

def globalProductChartDifference (V : X.left.Opens) (i : U.I₀) (hi : V ≤ (U.f i).opensRange) :=
  (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i V hi).iso.symm ≪≫
    (NormalizedProductRestrictions.globalNormalizedProductOnOpen k X e he V).iso

theorem globalProductChartDifference_reduction (V : X.left.Opens) (i : U.I₀)
    (hi : V ≤ (U.f i).opensRange) :
    (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).map (globalProductChartDifference k X U e he V i hi).hom = 𝟙 _ :=
  NormalizedProduct.Transitions.normalized_product_transition_fiber (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k))
    (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)) (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k)
    (Dual.OpenChart.dualFamilyOpenObject k X V) (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i V hi).iso
    (NormalizedProductRestrictions.globalNormalizedProductOnOpen k X e he V).iso
    (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i V hi).normalized
    (NormalizedProductRestrictions.globalNormalizedProductOnOpen k X e he V).normalized

theorem globalProductChartDifference_restriction {V W : X.left.Opens} (h : V ≤ W)
    (i : U.I₀) (hi : W ≤ (U.f i).opensRange) :
    (globalProductChartDifference k X U e he V i (h.trans hi)).hom ≫
        (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).map
          ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).map (Dual.OpenChart.dualFamilyOpenMap k X h)) =
      (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).map
          ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).map (Dual.OpenChart.dualFamilyOpenMap k X h)) ≫
        (globalProductChartDifference k X U e he W i hi).hom :=
  Product.ChartRestrictionSquares.productTransition_restriction_square (Dual.OpenChart.dualFamilyOpenMap k X h)
    ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).map
      ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).map (Dual.OpenChart.dualFamilyOpenMap k X h)))
    (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i V (h.trans hi)).iso
    (NormalizedProductRestrictions.globalNormalizedProductOnOpen k X e he V).iso
    (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i W hi).iso
    (NormalizedProductRestrictions.globalNormalizedProductOnOpen k X e he W).iso
    (Dual.CommonOpenRestriction.affineChartProductOnOpen_restriction k X U h i hi)
    (NormalizedProductRestrictions.globalNormalizedProductOnOpen_restriction k X e he h)

theorem globalProductChartDifference_cocycle (V : X.left.Opens) (i j : U.I₀)
    (hi : V ≤ (U.f i).opensRange) (hj : V ≤ (U.f j).opensRange) :
    DualOpen.CommonTransitions.dualCommonOpenTransition k X U V i j hi hj ≪≫ globalProductChartDifference k X U e he V j hj =
      globalProductChartDifference k X U e he V i hi := by
  apply Iso.ext
  simp only [DualOpen.CommonTransitions.dualCommonOpenTransition, globalProductChartDifference, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.ProductChartDifferences
