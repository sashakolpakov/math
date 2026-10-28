import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugePrimitive
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.LiteralAffineCover

/-! # Chart Gauge Local Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeLocalMaps

noncomputable section

/-! The adjusted charts give actual maps to the product of the global
special fiber. Their restrictions are controlled by the same adjusted
charts on literal smaller affine opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] CommonOpenFiber.dualCommonOpenFiber CommonOpenFiber.dualAffineCommonOpenFiber CommonOpenCoefficientRestriction.dualAffineCommonOpenMap
attribute [local implicit_reducible] ChartGauge.dualFamilyChartAffineOpen ChartGauge.dualChartGaugeParameters
attribute [local irreducible] DualOpen.CommonTransitions.affineChartProductOnOpen Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k)))) [Smooth X.hom]
    (U : X.left.AffineOpenCover) (a : ChartGauge.dualChartGaugeParameters k X U)

def dualChartGaugeLocalMap (i : U.I₀) :
    OpenChart.dualFamilyOpenObject k X (ChartGauge.dualFamilyChartAffineOpen k X U i).1 ⟶
      (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).obj X) :=
  (ChartGauge.dualChartGaugeOnOpen k X U a (ChartGauge.dualFamilyChartAffineOpen k X U i) i le_rfl).hom ≫
    (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).map
      ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).map
        (OpenChart.dualFamilyOpenInclusion k X (ChartGauge.dualFamilyChartAffineOpen k X U i).1))

theorem dualChartGaugeLocalMap_restrict (V : X.left.affineOpens) (i : U.I₀)
    (hi : V.1 ≤ (U.f i).opensRange) :
    OpenChart.dualFamilyOpenMap k X (show V.1 ≤ (ChartGauge.dualFamilyChartAffineOpen k X U i).1 from hi) ≫
        dualChartGaugeLocalMap k X U a i =
      (ChartGauge.dualChartGaugeOnOpen k X U a V i hi).hom ≫
        (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).map
          ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).map (OpenChart.dualFamilyOpenInclusion k X V.1)) := by
  let P := Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k) ⋙ Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)
  let W := ChartGauge.dualFamilyChartAffineOpen k X U i
  let j := OpenChart.dualFamilyOpenMap k X (show V.1 ≤ W.1 from hi)
  have hc : (ChartGauge.dualChartGaugeOnOpen k X U a V i hi).hom ≫ P.map j =
      j ≫ (ChartGauge.dualChartGaugeOnOpen k X U a W i le_rfl).hom :=
    ChartGauge.dualChartGaugeOnOpen_restriction k X U a hi i le_rfl
  change j ≫ ((ChartGauge.dualChartGaugeOnOpen k X U a W i le_rfl).hom ≫ P.map (OpenChart.dualFamilyOpenInclusion k X W.1)) = _
  calc
    j ≫ ((ChartGauge.dualChartGaugeOnOpen k X U a W i le_rfl).hom ≫ P.map (OpenChart.dualFamilyOpenInclusion k X W.1)) =
        ((ChartGauge.dualChartGaugeOnOpen k X U a V i hi).hom ≫ P.map j) ≫ P.map (OpenChart.dualFamilyOpenInclusion k X W.1) := by
      rw [hc, Category.assoc]
    _ = (ChartGauge.dualChartGaugeOnOpen k X U a V i hi).hom ≫ P.map (j ≫ OpenChart.dualFamilyOpenInclusion k X W.1) := by
      rw [P.map_comp, Category.assoc]
    _ = (ChartGauge.dualChartGaugeOnOpen k X U a V i hi).hom ≫ P.map (OpenChart.dualFamilyOpenInclusion k X V.1) := by
      rw [OpenChart.dualFamilyOpenMap_inclusion]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeLocalMaps
