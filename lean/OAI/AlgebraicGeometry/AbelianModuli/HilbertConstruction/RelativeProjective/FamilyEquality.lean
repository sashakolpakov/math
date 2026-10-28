import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.Pullbacks
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.AffineCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.OpenEquality

/-! # Family Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual embedded families in relative projective space are determined by all affine base pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Closed.Families.FlatClosedFamily.ext_affineProjective {T : Scheme.{u}} {n : ℕ}
    (F G : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver T n))
    (h : ∀ (R : CommRingCat.{u}) (x : Spec R ⟶ T),
      F.affineProjectivePullback x = G.affineProjectivePullback x) : F = G := by
  apply Closed.Families.FlatClosedFamily.ext
  apply ClosedFamily.OpenEquality.ideal_eq_of_open_cover (Projective.AffineCover.projectiveAffineOpenCover T.affineOpenCover n)
  intro i
  exact congrArg Closed.Families.FlatClosedFamily.ideal (h (T.affineOpenCover.X i) (T.affineOpenCover.f i))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
