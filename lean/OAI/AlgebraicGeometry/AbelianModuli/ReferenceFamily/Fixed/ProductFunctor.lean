import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentBasePoint
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverPullbackCartesianMap

/-! # Product Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Fixed.ProductFunctor

noncomputable section

/-! The actual fixed-fiber functor followed by the constant
dual-number product, retaining both original base changes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def fixedFamilyProductFunctor (k R : Type) [CommRing k] [CommRing R] [Algebra R k] :
    Over (Spec (.of R)) ⥤ Over (Spec (.of (DualNumber k))) :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⋙ Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)

instance fixedFamilyProductFunctor_preservesPullbacks (k R : Type) [CommRing k] [CommRing R] [Algebra R k] :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan (fixedFamilyProductFunctor k R) := by
  unfold fixedFamilyProductFunctor
  infer_instance

instance fixedFamilyProductFunctor_mapOpen (k R : Type) [CommRing k] [CommRing R] [Algebra R k]
    {X Y : Over (Spec (.of R))} (i : X ⟶ Y) [IsOpenImmersion i.left] :
    IsOpenImmersion ((fixedFamilyProductFunctor k R).map i).left := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap R k))
  have := OverPullbackCartesianMap.overPullback_map_open p i
  exact OverPullbackCartesianMap.overPullback_map_open (Smooth.AffineDualProduct.dualBaseProjection k) ((Over.pullback p).map i)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Fixed.ProductFunctor
