import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.CoefficientChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.Charts

/-! # Twisting Affine Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.TwistingAffinePullback

noncomputable section

/-! On every actual affine base chart, the relative projective twisting bundle becomes the standard projective O(1) over that chart's coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {R : CommRingCat.{u}} (x : Spec R ⟶ S) (n : ℕ)

def relativeProjectiveTwistingBundle_affineIso :
    ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).pullback (AffineProjective.Charts.affineProjectiveChartMap x n)).sheaf ≅
      (Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).sheaf := by
  let L := Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle Γ(S, ⊤) n
  let p := Limits.pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ
  exact (Scheme.Modules.pullbackComp (AffineProjective.Charts.affineProjectiveChartMap x n) p).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (AffineProjective.Charts.affineProjectiveChartMap_fst x n)).app L.sheaf ≪≫
      ProjectiveTwisting.CoefficientChange.affineProjectiveTwistingBundle_coefficientIso (AffineProjective.Charts.affinePointCoefficients x) n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.TwistingAffinePullback
