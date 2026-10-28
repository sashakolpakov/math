import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.PullbackAffineKernel
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Ideal Comap Affine Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.IdealComapAffineChart.BundleCycles

noncomputable section

/-! The actual pullback ideal sheaf has the extended kernel
ideal on every affine chart lying over an affine base chart. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem idealComap_affineChart {X Z Y : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : Y ⟶ X) (U : X.affineOpens) (V : Y.affineOpens) (h : V.1 ≤ f ⁻¹ᵁ U.1) :
    (i.ker.comap f).ideal V = (RingHom.ker (i.app U.1).hom).map (f.appLE U.1 V.1 h).hom := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i f, Scheme.Hom.ker_apply]
  exact Closed.PullbackAffineKernel.BundleCycles.closedPullback_affineChart_kernel i (pullback.fst f i) f (pullback.snd f i)
    (IsPullback.of_hasPullback f i) U V h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.IdealComapAffineChart.BundleCycles
