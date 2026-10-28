import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeLocalMaps

/-! # Chart Gauge Local Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeLocalOpen

noncomputable section

/-! The actual local maps defined by adjusted product charts are open
immersions into the product of the global special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] CommonOpenFiber.dualCommonOpenFiber CommonOpenFiber.dualAffineCommonOpenFiber
attribute [local irreducible] Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso DualOpen.CommonTransitions.affineChartProductOnOpen

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k)))) [Smooth X.hom]
    (U : X.left.AffineOpenCover) (a : ChartGauge.dualChartGaugeParameters k X U)

theorem dualChartGaugeLocalMap_open (i : U.I₀) : IsOpenImmersion (ChartGaugeLocalMaps.dualChartGaugeLocalMap k X U a i).left := by
  let W := ChartGauge.dualFamilyChartAffineOpen k X U i
  let j := OpenChart.dualFamilyOpenInclusion k X W.1
  let e := ChartGauge.dualChartGaugeOnOpen k X U a W i le_rfl
  let F := Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)
  let G := Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)
  have : IsOpenImmersion j.left := OpenChart.dualFamilyOpenInclusion_open k X W.1
  have : IsOpenImmersion (G.map j).left := OverPullbackCartesianMap.overPullback_map_open (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k) j
  have : IsOpenImmersion (F.map (G.map j)).left := OverPullbackCartesianMap.overPullback_map_open (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k) (G.map j)
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have : IsOpenImmersion e.hom.left := IsOpenImmersion.of_isIso _
  change IsOpenImmersion (e.hom.left ≫ (F.map (G.map j)).left)
  exact IsOpenImmersion.comp _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeLocalOpen
