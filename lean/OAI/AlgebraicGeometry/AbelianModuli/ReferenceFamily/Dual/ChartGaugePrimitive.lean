import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGauge
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.ChartGaugeCancellation

/-! # Chart Gauge Primitive -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugePrimitive

noncomputable section

/-! A literal primitive for the actual affine transition cocycle
makes all the constructed adjusted charts agree on their common opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] CommonOpenFiber.dualCommonOpenFiber CommonOpenFiber.dualAffineCommonOpenFiber
attribute [local implicit_reducible] CommonOpenCocycle.dualFamilyPairAffineOpen ChartGauge.dualChartGaugeParameters
attribute [local implicit_reducible] DualOpen.CommonTransitions.dualCommonOpenTransition CommonOpenDerivation.dualCommonOpenDerivation ChartGauge.dualChartGaugeOnOpen
attribute [local irreducible] DualOpen.CommonTransitions.affineChartProductOnOpen Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k)))) [Smooth X.hom] [IsSeparated X.hom]
    (U : X.left.AffineOpenCover) (a : ChartGauge.dualChartGaugeParameters k X U)

def IsDualChartGaugePrimitive : Prop := ∀ i j : U.I₀,
  CommonOpenCocycle.dualFamilyPairTransitionDerivation k X U i j =
    ChartGauge.dualChartGaugeCoefficient k X U a (CommonOpenCocycle.dualFamilyPairAffineOpen k X U i j) i inf_le_left -
      ChartGauge.dualChartGaugeCoefficient k X U a (CommonOpenCocycle.dualFamilyPairAffineOpen k X U i j) j inf_le_right

theorem dualChartGaugePrimitive_common_difference (ha : IsDualChartGaugePrimitive k X U a)
    (V : X.left.affineOpens) (i j : U.I₀) (hi : V.1 ≤ (U.f i).opensRange) (hj : V.1 ≤ (U.f j).opensRange) :
    CommonOpenDerivation.dualCommonOpenDerivation k X U V i j hi hj =
      ChartGauge.dualChartGaugeCoefficient k X U a V i hi - ChartGauge.dualChartGaugeCoefficient k X U a V j hj := by
  let W := CommonOpenCocycle.dualFamilyPairAffineOpen k X U i j
  have hV : V.1 ≤ W.1 := le_inf hi hj
  have ht := CommonOpenDerivationExtension.dualCommonOpenDerivation_restrict k X hV U i j inf_le_left inf_le_right
  calc
    CommonOpenDerivation.dualCommonOpenDerivation k X U V i j hi hj =
        CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X hV (CommonOpenCocycle.dualFamilyPairTransitionDerivation k X U i j) := ht.symm
    _ = CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X hV
        (ChartGauge.dualChartGaugeCoefficient k X U a W i inf_le_left - ChartGauge.dualChartGaugeCoefficient k X U a W j inf_le_right) :=
      congrArg (CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X hV) (ha i j)
    _ = CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X hV (ChartGauge.dualChartGaugeCoefficient k X U a W i inf_le_left) -
        CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X hV (ChartGauge.dualChartGaugeCoefficient k X U a W j inf_le_right) :=
      (CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X hV).map_sub _ _
    _ = ChartGauge.dualChartGaugeCoefficient k X U a V i hi - ChartGauge.dualChartGaugeCoefficient k X U a V j hj :=
      congrArg₂ (· - ·) (ChartGauge.dualChartGaugeCoefficient_restrict k X U a hV i inf_le_left)
        (ChartGauge.dualChartGaugeCoefficient_restrict k X U a hV j inf_le_right)

theorem dualChartGaugePrimitive_common_eq (ha : IsDualChartGaugePrimitive k X U a)
    (V : X.left.affineOpens) (i j : U.I₀) (hi : V.1 ≤ (U.f i).opensRange) (hj : V.1 ≤ (U.f j).opensRange) :
    ChartGauge.dualChartGaugeOnOpen k X U a V i hi = ChartGauge.dualChartGaugeOnOpen k X U a V j hj :=
  AffineProduct.ChartGaugeCancellation.affineProductChartGauge_cancellation k (CommonOpenFiber.dualAffineCommonOpenFiber k X V)
    (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i V.1 hi).iso (DualOpen.CommonTransitions.affineChartProductOnOpen k X U j V.1 hj).iso
    (DualOpen.CommonTransitions.dualCommonOpenTransition_reduction k X U V.1 i j hi hj)
    (ChartGauge.dualChartGaugeCoefficient k X U a V i hi) (ChartGauge.dualChartGaugeCoefficient k X U a V j hj)
    (dualChartGaugePrimitive_common_difference k X U a ha V i j hi hj)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugePrimitive
