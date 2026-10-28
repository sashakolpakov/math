import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeLocalMaps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverOpenCoverGluing

/-! # Chart Gauge Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeGluing

noncomputable section

/-! A literal cocycle primitive glues the constructed adjusted charts
into one actual map from the varying family to the product of its own
special fiber, over the original dual-number base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

attribute [local implicit_reducible] ChartGauge.dualFamilyChartAffineOpen CommonOpenCocycle.dualFamilyPairAffineOpen
attribute [local implicit_reducible] OpenChart.dualFamilyOpenObject OpenChart.dualFamilyOpenInclusion OpenChart.dualFamilyOpenMap
attribute [local irreducible] DualOpen.CommonTransitions.affineChartProductOnOpen Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k)))) [Smooth X.hom] [IsSeparated X.hom]
    (U : X.left.AffineOpenCover) (a : ChartGauge.dualChartGaugeParameters k X U) (ha : ChartGaugePrimitive.IsDualChartGaugePrimitive k X U a)

include ha

theorem dualChartGaugeLocalMaps_compatible (i j : U.I₀) :
    pullback.fst ((LiteralAffineCover.dualFamilyLiteralAffineCover k X U).f i) ((LiteralAffineCover.dualFamilyLiteralAffineCover k X U).f j) ≫
        (ChartGaugeLocalMaps.dualChartGaugeLocalMap k X U a i).left =
      pullback.snd _ _ ≫ (ChartGaugeLocalMaps.dualChartGaugeLocalMap k X U a j).left := by
  let V := CommonOpenCocycle.dualFamilyPairAffineOpen k X U i j
  have hl := ChartGaugeLocalMaps.dualChartGaugeLocalMap_restrict k X U a V i inf_le_left
  have hr := ChartGaugeLocalMaps.dualChartGaugeLocalMap_restrict k X U a V j inf_le_right
  have he := ChartGaugePrimitive.dualChartGaugePrimitive_common_eq k X U a ha V i j inf_le_left inf_le_right
  rw [he] at hl
  have hs := congrArg Over.Hom.left (hl.trans hr.symm)
  let hp := isPullback_opens_inf (ChartGauge.dualFamilyChartAffineOpen k X U i).1 (ChartGauge.dualFamilyChartAffineOpen k X U j).1
  apply (cancel_epi hp.isoPullback.hom).mp
  change hp.isoPullback.hom ≫ (pullback.fst _ _ ≫ (ChartGaugeLocalMaps.dualChartGaugeLocalMap k X U a i).left) =
    hp.isoPullback.hom ≫ (pullback.snd _ _ ≫ (ChartGaugeLocalMaps.dualChartGaugeLocalMap k X U a j).left)
  rw [← Category.assoc, hp.isoPullback_hom_fst, ← Category.assoc, hp.isoPullback_hom_snd]
  exact hs

def dualChartGaugeGluedMap : X ⟶
    (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).obj X) :=
  OverOpenCoverGluing.glueOverOpenCover X _ (LiteralAffineCover.dualFamilyLiteralAffineCover k X U)
    (fun i => (ChartGaugeLocalMaps.dualChartGaugeLocalMap k X U a i).left)
    (fun i => (ChartGaugeLocalMaps.dualChartGaugeLocalMap k X U a i).w)
    (dualChartGaugeLocalMaps_compatible k X U a ha)

theorem dualChartGaugeGluedMap_fac (i : U.I₀) :
    OpenChart.dualFamilyOpenInclusion k X (ChartGauge.dualFamilyChartAffineOpen k X U i).1 ≫
        dualChartGaugeGluedMap k X U a ha = ChartGaugeLocalMaps.dualChartGaugeLocalMap k X U a i := by
  apply Over.OverMorphism.ext
  exact OverOpenCoverGluing.glueOverOpenCover_fac X _ (LiteralAffineCover.dualFamilyLiteralAffineCover k X U)
    (fun j => (ChartGaugeLocalMaps.dualChartGaugeLocalMap k X U a j).left)
    (fun j => (ChartGaugeLocalMaps.dualChartGaugeLocalMap k X U a j).w)
    (dualChartGaugeLocalMaps_compatible k X U a ha) i

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeGluing
