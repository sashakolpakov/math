import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGaugeGlobalProduct
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.ProductTransitionPrimitive

/-! # Product Primitive Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductPrimitiveCriterion

noncomputable section

/-! A smooth separated family over dual numbers is a normalized product
exactly when its actual affine transition cocycle has a literal primitive. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local irreducible] Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso DualOpen.CommonTransitions.affineChartProductOnOpen

theorem normalizedDualProduct_iff_transitionPrimitive (k : Type) [Field k]
    (X : Over (Spec (.of (DualNumber k)))) [Smooth X.hom] [IsSeparated X.hom]
    (U : X.left.AffineOpenCover) :
    (∃ e : X ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).obj X),
      NormalizedDual.OpenProductData.NormalizesDualProductFiber k e) ↔
      ∃ a : ChartGauge.dualChartGaugeParameters k X U, ChartGaugePrimitive.IsDualChartGaugePrimitive k X U a := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨Global.ProductTransitionPrimitive.globalProductGaugeParameters k X U e he, Global.ProductTransitionPrimitive.globalProductGaugeParameters_primitive k X U e he⟩
  · rintro ⟨a, ha⟩
    obtain ⟨e, he, _⟩ := ChartGaugeGlobalProduct.exists_dualChartGaugeGlobalProduct k X U a ha
    exact ⟨e, he⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductPrimitiveCriterion
