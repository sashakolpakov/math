import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons
import Mathlib.AlgebraicGeometry.Gluing

/-! # Hom Open Cover Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.HomOpenCoverDetection

noncomputable section

/-! Actual relative morphisms are detected by base change along an open cover of the base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u v

theorem overHom_eq_of_openCoverPullbacks {S : Scheme.{u}} {A B : Over S}
    (C : Scheme.OpenCover.{v} S) (f g : A ⟶ B)
    (h : ∀ i, (Over.pullback (C.f i)).map f = (Over.pullback (C.f i)).map g) : f = g := by
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (C.pullback₁ A.hom)
  intro i
  change pullback.fst A.hom (C.f i) ≫ f.left = pullback.fst A.hom (C.f i) ≫ g.left
  exact (Pullback.Comparisons.overPullback_map_left_fst f (C.f i)).symm.trans
    ((congrArg (fun q : (Over.pullback (C.f i)).obj A ⟶ (Over.pullback (C.f i)).obj B =>
      q.left ≫ pullback.fst B.hom (C.f i)) (h i)).trans (Pullback.Comparisons.overPullback_map_left_fst g (C.f i)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.HomOpenCoverDetection
