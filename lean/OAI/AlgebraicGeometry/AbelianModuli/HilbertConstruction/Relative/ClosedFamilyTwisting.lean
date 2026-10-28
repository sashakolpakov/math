import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.TwistingAffinePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdentityAffineFamilyComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.TwistingBundle

/-! # Closed Family Twisting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The relative twisting bundle on an actual closed projective family matches the ordinary projective O(1) on its identity affine presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def Closed.Families.FlatClosedFamily.relativeTwistingBundle {S : Scheme.{u}} {n : ℕ} (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver S n)) :
    Line.Bundles.LineBundle F.scheme.left :=
  (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).pullback F.inclusion.left

variable {R : CommRingCat.{u}} {n : ℕ} (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver (Spec R) n))

def Closed.Families.FlatClosedFamily.identityAffineTwistingBundleIso :
    (F.relativeTwistingBundle.pullback F.identityAffineFamilyIso.hom.left).sheaf ≅
      (F.affineProjectivePullback (𝟙 _)).twistingBundle.sheaf := by
  let L := RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec R) n
  let G := F.affineProjectivePullback (𝟙 _)
  let a := AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec R)) n
  exact (Scheme.Modules.pullbackComp F.identityAffineFamilyIso.hom.left F.inclusion.left).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr F.identityAffineFamilyIso_embedding).app L.sheaf ≪≫
    (Scheme.Modules.pullbackComp G.inclusion.left a).symm.app L.sheaf ≪≫
    (Scheme.Modules.pullback G.inclusion.left).mapIso (Relative.TwistingAffinePullback.relativeProjectiveTwistingBundle_affineIso (𝟙 (Spec R)) n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
