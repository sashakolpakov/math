import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.PullbackSquare

/-! # Adjunction Unit -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.AdjunctionUnit.OpenPullbackSquare

noncomputable section

/-! Compatibility of the actual pullback unit with restriction to an open subscheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

theorem unit_square (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      (OpenModule.BaseChangeMate.OpenPullbackSquare.openBaseChangeMap f U).app ((Scheme.Modules.pullback f).obj M) =
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        ((OpenModule.PullbackSquare.OpenPullbackSquare.adjointPullbackSquare f U).hom.app M) := by
  have h := unit_mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
    (TwoSquare.mk _ _ _ _ (OpenModule.PullbackSquare.OpenPullbackSquare.adjointPullbackSquare f U).hom) M
  change _ ≫
    ((mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
      (TwoSquare.mk _ _ _ _ (OpenModule.PullbackSquare.OpenPullbackSquare.adjointPullbackSquare f U).hom)).natTrans).app _ = _ at h
  rw [OpenModule.PullbackSquare.OpenPullbackSquare.rightMate] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.AdjunctionUnit.OpenPullbackSquare
