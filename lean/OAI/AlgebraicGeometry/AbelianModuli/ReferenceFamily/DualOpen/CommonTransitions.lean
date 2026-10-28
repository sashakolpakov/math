import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.OpenChart
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SelectedDualAffineProducts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductRestriction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.Transitions

/-! # Common Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.CommonTransitions

noncomputable section

section

/-! The constructed affine-cover product charts restrict to the literal
open subfamilies of the original varying family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] NormalizedDual.OpenProductData.NormalizesProductFiber
attribute [local irreducible] Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k))))
    (U : X.left.AffineOpenCover) (i : U.I₀) (V : X.left.Opens)

variable [Smooth X.hom]

def affineChartProductOnOpen (hV : V ≤ (U.f i).opensRange) := by
  have := Dual.OpenChart.dualFamilyOpenLiftToChart_open k X U i V hV
  exact NormalizedDual.OpenProductRestriction.restrictNormalizedDualProduct k (Dual.OpenChart.dualFamilyOpenLiftToChart k X U i V hV)
    (SelectedDualAffineProducts.selectedSmoothDualAffineChartProduct k X U i)
    (SelectedDualAffineProducts.selectedSmoothDualAffineChartProduct_normalized k X U i)

end

/-! Actual product-chart transitions on one literal common open of
the varying family, with their scheme cocycle and exact reduction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] NormalizedDual.OpenProductData.NormalizesProductFiber
attribute [local irreducible] Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k)))) [Smooth X.hom]
    (U : X.left.AffineOpenCover) (V : X.left.Opens)

def dualCommonOpenTransition (i j : U.I₀)
    (hi : V ≤ (U.f i).opensRange) (hj : V ≤ (U.f j).opensRange) :=
  (affineChartProductOnOpen k X U i V hi).iso.symm ≪≫
    (affineChartProductOnOpen k X U j V hj).iso

theorem dualCommonOpenTransition_cocycle (i j l : U.I₀)
    (hi : V ≤ (U.f i).opensRange) (hj : V ≤ (U.f j).opensRange)
    (hl : V ≤ (U.f l).opensRange) :
    dualCommonOpenTransition k X U V i j hi hj ≪≫ dualCommonOpenTransition k X U V j l hj hl =
      dualCommonOpenTransition k X U V i l hi hl := by
  apply Iso.ext
  simp only [dualCommonOpenTransition, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]

theorem dualCommonOpenTransition_reduction (i j : U.I₀)
    (hi : V ≤ (U.f i).opensRange) (hj : V ≤ (U.f j).opensRange) :
    (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).map (dualCommonOpenTransition k X U V i j hi hj).hom =
      𝟙 ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).obj
        ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).obj
          ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).obj (Dual.OpenChart.dualFamilyOpenObject k X V)))) := by
  exact NormalizedProduct.Transitions.normalized_product_transition_fiber (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k))
    (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)) (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k)
    (Dual.OpenChart.dualFamilyOpenObject k X V)
    (affineChartProductOnOpen k X U i V hi).iso (affineChartProductOnOpen k X U j V hj).iso
    (affineChartProductOnOpen k X U i V hi).normalized (affineChartProductOnOpen k X U j V hj).normalized

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.CommonTransitions
