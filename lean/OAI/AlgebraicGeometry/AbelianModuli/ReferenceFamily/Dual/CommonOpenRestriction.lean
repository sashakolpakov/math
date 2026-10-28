import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.CommonTransitions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartRestrictionSquares

/-! # Common Open Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenRestriction

noncomputable section

/-! The selected normalized charts and their actual transition maps
commute with restriction to any smaller literal open of the family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local irreducible] Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k))))
    (U : X.left.AffineOpenCover) {V W : X.left.Opens} (h : V ≤ W)

theorem dualFamilyOpenMap_open : IsOpenImmersion (OpenChart.dualFamilyOpenMap k X h).left :=
  inferInstanceAs (IsOpenImmersion (X.left.homOfLE h))

theorem dualFamilyOpenLiftToChart_composition (i : U.I₀) (hi : W ≤ (U.f i).opensRange) :
    OpenChart.dualFamilyOpenMap k X h ≫ OpenChart.dualFamilyOpenLiftToChart k X U i W hi =
      OpenChart.dualFamilyOpenLiftToChart k X U i V (h.trans hi) := by
  have := OpenChart.dualFamilyAffineChartInclusion_open k X U i
  have : Mono (ReferenceFamily.Smooth.DualAffineCover.dualFamilyAffineChartInclusion k X U i) :=
    Over.mono_of_mono_left (ReferenceFamily.Smooth.DualAffineCover.dualFamilyAffineChartInclusion k X U i)
  apply (cancel_mono (ReferenceFamily.Smooth.DualAffineCover.dualFamilyAffineChartInclusion k X U i)).mp
  rw [Category.assoc, OpenChart.dualFamilyOpenLiftToChart_fac, OpenChart.dualFamilyOpenMap_inclusion,
    OpenChart.dualFamilyOpenLiftToChart_fac]

variable [Smooth X.hom]

theorem affineChartProductOnOpen_restriction (i : U.I₀) (hi : W ≤ (U.f i).opensRange) :
    (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i V (h.trans hi)).iso.hom ≫
        (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).map
          ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).map (OpenChart.dualFamilyOpenMap k X h)) =
      OpenChart.dualFamilyOpenMap k X h ≫ (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i W hi).iso.hom := by
  let P := Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k) ⋙ Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)
  have := OpenChart.dualFamilyOpenLiftToChart_open k X U i W hi
  have : Mono (OpenChart.dualFamilyOpenLiftToChart k X U i W hi) :=
    Over.mono_of_mono_left (OpenChart.dualFamilyOpenLiftToChart k X U i W hi)
  have : Mono (P.map (OpenChart.dualFamilyOpenLiftToChart k X U i W hi)) := inferInstance
  exact Product.ChartRestrictionSquares.productChart_restriction_square P (OpenChart.dualFamilyOpenMap k X h)
    (OpenChart.dualFamilyOpenLiftToChart k X U i W hi) (OpenChart.dualFamilyOpenLiftToChart k X U i V (h.trans hi))
    (dualFamilyOpenLiftToChart_composition k X U h i hi) (SelectedDualAffineProducts.selectedSmoothDualAffineChartProduct k X U i)
    (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i V (h.trans hi)).iso (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i W hi).iso
    (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i V (h.trans hi)).commutes
    (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i W hi).commutes

theorem dualCommonOpenTransition_restriction (i j : U.I₀)
    (hi : W ≤ (U.f i).opensRange) (hj : W ≤ (U.f j).opensRange) :
    (DualOpen.CommonTransitions.dualCommonOpenTransition k X U V i j (h.trans hi) (h.trans hj)).hom ≫
        (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).map
          ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).map (OpenChart.dualFamilyOpenMap k X h)) =
      (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).map
          ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).map (OpenChart.dualFamilyOpenMap k X h)) ≫
        (DualOpen.CommonTransitions.dualCommonOpenTransition k X U W i j hi hj).hom :=
  Product.ChartRestrictionSquares.productTransition_restriction_square (OpenChart.dualFamilyOpenMap k X h)
    ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).map
      ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).map (OpenChart.dualFamilyOpenMap k X h)))
    (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i V (h.trans hi)).iso
    (DualOpen.CommonTransitions.affineChartProductOnOpen k X U j V (h.trans hj)).iso
    (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i W hi).iso (DualOpen.CommonTransitions.affineChartProductOnOpen k X U j W hj).iso
    (affineChartProductOnOpen_restriction k X U h i hi)
    (affineChartProductOnOpen_restriction k X U h j hj)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenRestriction
