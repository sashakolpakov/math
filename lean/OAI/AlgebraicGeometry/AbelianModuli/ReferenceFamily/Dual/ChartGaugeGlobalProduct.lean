import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeGluedFiber
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeGluedOpen
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductIsoExistence

/-! # Chart Gauge Global Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeGlobalProduct

noncomputable section

/-! A literal primitive of the constructed affine transition cocycle
produces an actual global product isomorphism over the original dual-number
base, normalized on the actual special fiber and retaining the exact glued map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local irreducible] Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso DualOpen.CommonTransitions.affineChartProductOnOpen

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k)))) [Smooth X.hom] [IsSeparated X.hom]
    (U : X.left.AffineOpenCover) (a : ChartGauge.dualChartGaugeParameters k X U) (ha : ChartGaugePrimitive.IsDualChartGaugePrimitive k X U a)

theorem exists_dualChartGaugeGlobalProduct :
    type_of% (NormalizedDual.ProductIsoExistence.exists_normalized_dualProductIso_of_openCharts k X (ChartGaugeGluing.dualChartGaugeGluedMap k X U a ha)
      (ChartGaugeGluedFiber.dualChartGaugeGluedMap_normalized k X U a ha) (LiteralAffineCover.dualFamilyLiteralAffineCover k X U)
      (ChartGaugeGluedOpen.dualChartGaugeGluedMap_chart_open k X U a ha)) :=
  NormalizedDual.ProductIsoExistence.exists_normalized_dualProductIso_of_openCharts k X (ChartGaugeGluing.dualChartGaugeGluedMap k X U a ha)
    (ChartGaugeGluedFiber.dualChartGaugeGluedMap_normalized k X U a ha) (LiteralAffineCover.dualFamilyLiteralAffineCover k X U)
    (ChartGaugeGluedOpen.dualChartGaugeGluedMap_chart_open k X U a ha)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeGlobalProduct
