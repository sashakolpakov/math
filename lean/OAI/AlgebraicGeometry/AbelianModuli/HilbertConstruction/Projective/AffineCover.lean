import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.Charts

/-! # Affine Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.AffineCover

noncomputable section

/-! Relative projective space is covered by the standard projective spaces of an affine base cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def projectiveAffineOpenCover {S : Scheme.{u}} (C : S.AffineOpenCover) (n : ℕ) :
    (ProjectivePresentations.projectiveSpaceOver S n).left.OpenCover :=
  Scheme.Cover.copy (C.openCover.pullback₁ (ProjectivePresentations.projectiveSpaceOver S n).hom) C.I₀
    (fun i => (ProjectivePresentations.affineProjectiveSpace (C.X i) n).left)
    (fun i => AffineProjective.Charts.affineProjectiveChartMap (C.f i) n) (Equiv.refl _)
    (fun i => (AffineProjective.Charts.affineProjectiveChartMap_isPullback (C.f i) n).isoPullback)
    (fun i => (AffineProjective.Charts.affineProjectiveChartMap_isPullback (C.f i) n).isoPullback_hom_fst.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.AffineCover
