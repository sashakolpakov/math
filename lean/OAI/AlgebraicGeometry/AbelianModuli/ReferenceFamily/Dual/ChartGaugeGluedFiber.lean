import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeGluing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.LocalTriangle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReducedCoverHomExt
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.MapComparison

/-! # Chart Gauge Glued Fiber -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeGluedFiber

noncomputable section

/-! The glued actual chart map retains the original canonical
normalization on the special fiber. This is checked on its constructed
base-changed affine cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] CommonOpenFiber.dualCommonOpenFiber CommonOpenFiber.dualAffineCommonOpenFiber
attribute [local irreducible] Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso DualOpen.CommonTransitions.affineChartProductOnOpen

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k)))) [Smooth X.hom] [IsSeparated X.hom]
    (U : X.left.AffineOpenCover) (a : ChartGauge.dualChartGaugeParameters k X U) (ha : ChartGaugePrimitive.IsDualChartGaugePrimitive k X U a)

theorem dualChartGaugeGluedMap_normalized :
    (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).map (ChartGaugeGluing.dualChartGaugeGluedMap k X U a ha) ≫
        (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k).hom.app ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).obj X) = 𝟙 _ := by
  let F := Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)
  let G := Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)
  let n := ProductComparisonRepresentative.dualProductComparisonRepresentative k
  have hn : n = Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k := ProductComparisonRepresentative.dualProductComparisonRepresentative_eq k
  let f := ChartGaugeGluing.dualChartGaugeGluedMap k X U a ha
  have hnorm : G.map f ≫ n.hom.app (G.obj X) = 𝟙 _ := by
    apply ReducedCoverHomExt.dualReducedLiteralCover_hom_ext k X U
    intro i
    let W := ChartGauge.dualFamilyChartAffineOpen k X U i
    let j := OpenChart.dualFamilyOpenInclusion k X W.1
    let e := ChartGauge.dualChartGaugeOnOpen k X U a W i le_rfl
    have he : NormalizedDual.OpenProductData.NormalizesProductFiber F G n e :=
      (congrArg (fun q => NormalizedDual.OpenProductData.NormalizesProductFiber F G q e) hn).mpr
        (ChartGauge.dualChartGaugeOnOpen_normalized k X U a W i le_rfl)
    have hc := NormalizedProduct.LocalTriangle.normalizedProduct_local_triangle F G n j e he f (ChartGaugeGluing.dualChartGaugeGluedMap_fac k X U a ha i)
    have hh : G.map j ≫ (G.map f ≫ n.hom.app (G.obj X)) = G.map j ≫ 𝟙 (G.obj X) :=
      hc.trans (Category.comp_id _).symm
    exact hh
  have hout := NormalizedProduct.MapComparison.normalizedProductMap_comparison_congr F G n (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k) hn f hnorm
  exact hout

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeGluedFiber
