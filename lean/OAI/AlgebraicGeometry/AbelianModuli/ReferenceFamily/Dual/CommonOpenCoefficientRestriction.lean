import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenCocycle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenRestriction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.DerivationNaturality

/-! # Common Open Coefficient Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenCoefficientRestriction

noncomputable section

/-! The derivations on actual common affine opens commute with the
actual coefficient-ring restriction maps on their scheme special fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] CommonOpenFiber.dualCommonOpenFiber CommonOpenFiber.dualAffineCommonOpenFiber

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k))))
    {V W : X.left.affineOpens} (h : V.1 ≤ W.1)

def dualAffineCommonOpenMap : CommonOpenFiber.dualAffineCommonOpenFiber k X V ⟶ CommonOpenFiber.dualAffineCommonOpenFiber k X W :=
  (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).map (OpenChart.dualFamilyOpenMap k X h)

def dualAffineCommonOpenAlgebraMap :
    HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X W) →ₐ[k]
      HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X V) :=
  HilbertConstruction.Affine.OverMorphisms.affineOverMap k (X := CommonOpenFiber.dualAffineCommonOpenFiber k X V) (Y := CommonOpenFiber.dualAffineCommonOpenFiber k X W)
    (dualAffineCommonOpenMap k X h)

theorem dualAffineCommonOpenMap_open : IsOpenImmersion (dualAffineCommonOpenMap k X h).left := by
  have := CommonOpenRestriction.dualFamilyOpenMap_open k X h
  exact OverPullbackCartesianMap.overPullback_map_open (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k) (OpenChart.dualFamilyOpenMap k X h)

variable [Smooth X.hom] (U : X.left.AffineOpenCover)

theorem dualCommonOpenDerivation_natural (i j : U.I₀)
    (hi : W.1 ≤ (U.f i).opensRange) (hj : W.1 ≤ (U.f j).opensRange)
    (a : HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X W)) :
    type_of% (AffineProduct.DerivationNaturality.affineProductTransitionDerivation_natural k
    (X := CommonOpenFiber.dualAffineCommonOpenFiber k X V) (Y := CommonOpenFiber.dualAffineCommonOpenFiber k X W)
    (dualAffineCommonOpenMap k X h)
    (DualOpen.CommonTransitions.dualCommonOpenTransition k X U V.1 i j (h.trans hi) (h.trans hj))
    (DualOpen.CommonTransitions.dualCommonOpenTransition k X U W.1 i j hi hj)
    (DualOpen.CommonTransitions.dualCommonOpenTransition_reduction k X U V.1 i j (h.trans hi) (h.trans hj))
    (DualOpen.CommonTransitions.dualCommonOpenTransition_reduction k X U W.1 i j hi hj)
    (CommonOpenRestriction.dualCommonOpenTransition_restriction k X U h i j hi hj) a) :=
  AffineProduct.DerivationNaturality.affineProductTransitionDerivation_natural k
    (X := CommonOpenFiber.dualAffineCommonOpenFiber k X V) (Y := CommonOpenFiber.dualAffineCommonOpenFiber k X W)
    (dualAffineCommonOpenMap k X h)
    (DualOpen.CommonTransitions.dualCommonOpenTransition k X U V.1 i j (h.trans hi) (h.trans hj))
    (DualOpen.CommonTransitions.dualCommonOpenTransition k X U W.1 i j hi hj)
    (DualOpen.CommonTransitions.dualCommonOpenTransition_reduction k X U V.1 i j (h.trans hi) (h.trans hj))
    (DualOpen.CommonTransitions.dualCommonOpenTransition_reduction k X U W.1 i j hi hj)
    (CommonOpenRestriction.dualCommonOpenTransition_restriction k X U h i j hi hj) a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenCoefficientRestriction
