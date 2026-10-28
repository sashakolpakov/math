import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.RingPullbackMapDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Hom Local Ring Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.HomLocalRingDetection

noncomputable section

/-! Relative morphisms over arbitrary bases are detected after all local-ring-valued base changes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem overHom_eq_of_allLocalRingPullbacks {S : Scheme.{u}} {X Y : Over S}
    (f g : X ⟶ Y)
    (h : ∀ (R : Type u) [CommRing R] [IsLocalRing R] (b : Spec (.of R) ⟶ S),
      (Over.pullback b).map f = (Over.pullback b).map g) : f = g := by
  apply Over.OverMorphism.ext
  apply Local.RingPullbackMapDetection.schemeMap_eq_of_localRingPullbacks X.hom
  intro R _ _ b
  exact (Pullback.Comparisons.overPullback_map_left_fst f b).symm.trans
    ((congrArg (fun q : (Over.pullback b).obj X ⟶ (Over.pullback b).obj Y =>
      q.left ≫ pullback.fst Y.hom b) (h R b)).trans (Pullback.Comparisons.overPullback_map_left_fst g b))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.HomLocalRingDetection
