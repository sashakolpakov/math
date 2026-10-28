import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.ProductDifferenceCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugePrimitive

/-! # Product Transition Primitive -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.ProductTransitionPrimitive

noncomputable section

/-! Restricting an actual normalized global product recovers a literal
primitive of the selected affine transition cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] Dual.CommonOpenFiber.dualCommonOpenFiber Dual.CommonOpenFiber.dualAffineCommonOpenFiber
attribute [local implicit_reducible] Dual.ChartGauge.dualFamilyChartAffineOpen Dual.CommonOpenCocycle.dualFamilyPairAffineOpen Dual.ChartGauge.dualChartGaugeParameters
attribute [local irreducible] DualOpen.CommonTransitions.affineChartProductOnOpen Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k)))) [Smooth X.hom]
    (U : X.left.AffineOpenCover)
    (e : X ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).obj X))
    (he : NormalizedDual.OpenProductData.NormalizesDualProductFiber k e)

def globalProductGaugeParameters : Dual.ChartGauge.dualChartGaugeParameters k X U :=
  fun i => ProductDifferenceCoefficients.globalProductDifferenceCoefficient k X U e he (Dual.ChartGauge.dualFamilyChartAffineOpen k X U i) i le_rfl

theorem globalProductGaugeCoefficient_eq (V : X.left.affineOpens) (i : U.I₀)
    (hi : V.1 ≤ (U.f i).opensRange) :
    Dual.ChartGauge.dualChartGaugeCoefficient k X U (globalProductGaugeParameters k X U e he) V i hi =
      ProductDifferenceCoefficients.globalProductDifferenceCoefficient k X U e he V i hi :=
  ProductDifferenceCoefficients.globalProductDifferenceCoefficient_restrict k X U e he
    (show V.1 ≤ (Dual.ChartGauge.dualFamilyChartAffineOpen k X U i).1 from hi) i le_rfl

theorem globalProductDifferenceCoefficient_cocycle (V : X.left.affineOpens) (i j : U.I₀)
    (hi : V.1 ≤ (U.f i).opensRange) (hj : V.1 ≤ (U.f j).opensRange) :
    Dual.CommonOpenDerivation.dualCommonOpenDerivation k X U V i j hi hj + ProductDifferenceCoefficients.globalProductDifferenceCoefficient k X U e he V j hj =
      ProductDifferenceCoefficients.globalProductDifferenceCoefficient k X U e he V i hi := by
  let G := Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)
  have hcomp : G.map ((DualOpen.CommonTransitions.dualCommonOpenTransition k X U V.1 i j hi hj ≪≫
      ProductChartDifferences.globalProductChartDifference k X U e he V.1 j hj).hom) = 𝟙 _ := by
    rw [ProductChartDifferences.globalProductChartDifference_cocycle]
    exact ProductChartDifferences.globalProductChartDifference_reduction k X U e he V.1 i hi
  have hd := AffineProduct.DerivationLaws.affineProductTransitionDerivation_trans k (Dual.CommonOpenFiber.dualAffineCommonOpenFiber k X V)
    (DualOpen.CommonTransitions.dualCommonOpenTransition k X U V.1 i j hi hj) (ProductChartDifferences.globalProductChartDifference k X U e he V.1 j hj)
    (DualOpen.CommonTransitions.dualCommonOpenTransition_reduction k X U V.1 i j hi hj)
    (ProductChartDifferences.globalProductChartDifference_reduction k X U e he V.1 j hj) hcomp
  exact hd.symm.trans (AffineProduct.DerivationLaws.affineProductTransitionDerivation_congr k (Dual.CommonOpenFiber.dualAffineCommonOpenFiber k X V)
    _ _ hcomp (ProductChartDifferences.globalProductChartDifference_reduction k X U e he V.1 i hi)
    (ProductChartDifferences.globalProductChartDifference_cocycle k X U e he V.1 i j hi hj))

variable [IsSeparated X.hom]

theorem globalProductGaugeParameters_primitive :
    Dual.ChartGaugePrimitive.IsDualChartGaugePrimitive k X U (globalProductGaugeParameters k X U e he) := by
  intro i j
  rw [globalProductGaugeCoefficient_eq, globalProductGaugeCoefficient_eq]
  exact eq_sub_iff_add_eq.mpr (globalProductDifferenceCoefficient_cocycle k X U e he
    (Dual.CommonOpenCocycle.dualFamilyPairAffineOpen k X U i j) i j inf_le_left inf_le_right)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.ProductTransitionPrimitive
