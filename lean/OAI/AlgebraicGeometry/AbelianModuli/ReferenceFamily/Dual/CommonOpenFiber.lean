import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.OpenChart
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.VaryingDualReduction

/-! # Common Open Fiber -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenFiber

noncomputable section

/-! The coefficient scheme on a literal affine common open is the
actual special fiber of that open, and is itself affine. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k))))
    (V : X.left.Opens)

def dualCommonOpenFiber : Over (Spec (.of k)) :=
  (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj (OpenChart.dualFamilyOpenObject k X V)

theorem dualCommonOpenFiber_affine (hV : IsAffineOpen V) :
    IsAffine (dualCommonOpenFiber k X V).left := by
  have : IsAffine (OpenChart.dualFamilyOpenObject k X V).left := OpenChart.dualFamilyOpenObject_affine k X V hV
  have := VaryingDualReduction.dualFamilyReduction_closed k (OpenChart.dualFamilyOpenObject k X V)
  have : IsAffineHom (VaryingDualReduction.dualFamilyReduction k (OpenChart.dualFamilyOpenObject k X V)) := inferInstance
  change IsAffine ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj (OpenChart.dualFamilyOpenObject k X V)).left
  exact isAffine_of_isAffineHom (VaryingDualReduction.dualFamilyReduction k (OpenChart.dualFamilyOpenObject k X V))

def dualAffineCommonOpenFiber (W : X.left.affineOpens) : Over (Spec (.of k)) :=
  dualCommonOpenFiber k X W.1

instance dualAffineCommonOpenFiber_affine (W : X.left.affineOpens) :
    IsAffine (dualAffineCommonOpenFiber k X W).left :=
  dualCommonOpenFiber_affine k X W.1 W.2

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenFiber
