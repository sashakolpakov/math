import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeLocalOpen
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeGluing

/-! # Chart Gauge Glued Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeGluedOpen

noncomputable section

/-! The glued actual map is an open immersion on every literal affine
chart because its restriction is the already constructed local chart map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k)))) [Smooth X.hom] [IsSeparated X.hom]
    (U : X.left.AffineOpenCover) (a : ChartGauge.dualChartGaugeParameters k X U) (ha : ChartGaugePrimitive.IsDualChartGaugePrimitive k X U a)

theorem dualChartGaugeGluedMap_chart_open (i : U.I₀) :
    IsOpenImmersion ((LiteralAffineCover.dualFamilyLiteralAffineCover k X U).f i ≫ (ChartGaugeGluing.dualChartGaugeGluedMap k X U a ha).left) := by
  have h : (LiteralAffineCover.dualFamilyLiteralAffineCover k X U).f i ≫ (ChartGaugeGluing.dualChartGaugeGluedMap k X U a ha).left =
      (ChartGaugeLocalMaps.dualChartGaugeLocalMap k X U a i).left :=
    congrArg Over.Hom.left (ChartGaugeGluing.dualChartGaugeGluedMap_fac k X U a ha i)
  exact h.symm ▸ ChartGaugeLocalOpen.dualChartGaugeLocalMap_open k X U a i

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeGluedOpen
