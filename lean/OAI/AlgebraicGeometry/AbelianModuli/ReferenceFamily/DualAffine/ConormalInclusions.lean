import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AffineDerivationPresheaf
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OpenConormalCoordinates

/-! # Conormal Inclusions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.ConormalInclusions

noncomputable section

/-! The coefficient schemes of actual affine opens embed into the
actual special fiber. These inclusions commute with the existing
coefficient restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] Dual.CommonOpenFiber.dualCommonOpenFiber Dual.CommonOpenFiber.dualAffineCommonOpenFiber

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k))))

abbrev dualFamilySpecialFiberObject : Over (Spec (.of k)) :=
  (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X

def dualAffineCommonOpenInclusion (V : X.left.affineOpens) :
    Dual.CommonOpenFiber.dualAffineCommonOpenFiber k X V ⟶ (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X :=
  (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (Dual.OpenChart.dualFamilyOpenInclusion k X V.1)

instance dualAffineCommonOpenInclusion_open (V : X.left.affineOpens) :
    IsOpenImmersion (dualAffineCommonOpenInclusion k X V).left := by
  have := Dual.OpenChart.dualFamilyOpenInclusion_open k X V.1
  exact OverPullbackCartesianMap.overPullback_map_open (Smooth.AffineDualProduct.dualBaseReduction k) (Dual.OpenChart.dualFamilyOpenInclusion k X V.1)

theorem dualAffineCommonOpenInclusion_natural {V W : X.left.affineOpens} (h : V.1 ≤ W.1) :
    Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenMap k X h ≫ dualAffineCommonOpenInclusion k X W =
      dualAffineCommonOpenInclusion k X V := by
  change (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (Dual.OpenChart.dualFamilyOpenMap k X h) ≫
      (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (Dual.OpenChart.dualFamilyOpenInclusion k X W.1) =
    (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (Dual.OpenChart.dualFamilyOpenInclusion k X V.1)
  rw [← CategoryTheory.Functor.map_comp, Dual.OpenChart.dualFamilyOpenMap_inclusion]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.ConormalInclusions
