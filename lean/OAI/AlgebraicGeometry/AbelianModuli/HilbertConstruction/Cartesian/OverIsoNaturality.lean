import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.PullbackRecoveryIso

/-! # Over Iso Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OverIsoNaturality

noncomputable section

/-! Canonical isomorphisms from Cartesian models to categorical pullbacks preserve every compatible family morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem cartesianAmbientOverIso_natural
    {S T : Scheme.{u}} (f : T ⟶ S) {X Y : Over S} {X' Y' : Over T}
    (qX : X'.left ⟶ X.left) (qY : Y'.left ⟶ Y.left)
    (hX : IsPullback qX X'.hom X.hom f) (hY : IsPullback qY Y'.hom Y.hom f)
    (i : X' ⟶ Y') (j : X ⟶ Y) (hw : qX ≫ j.left = i.left ≫ qY) :
    (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso qX f hX).hom ≫ (Over.pullback f).map j =
      i ≫ (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso qY f hY).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hj : ((Over.pullback f).map j).left ≫ pullback.fst Y.hom f =
        pullback.fst X.hom f ≫ j.left := pullback.lift_fst _ _ _
    change (hX.isoPullback.hom ≫ ((Over.pullback f).map j).left) ≫ pullback.fst Y.hom f =
      (i.left ≫ hY.isoPullback.hom) ≫ pullback.fst Y.hom f
    rw [Category.assoc, hj, ← Category.assoc, hX.isoPullback_hom_fst, Category.assoc, hY.isoPullback_hom_fst]
    exact hw
  · exact ((ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso qX f hX).hom ≫ (Over.pullback f).map j).w.trans
      ((i ≫ (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso qY f hY).hom).w.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OverIsoNaturality
