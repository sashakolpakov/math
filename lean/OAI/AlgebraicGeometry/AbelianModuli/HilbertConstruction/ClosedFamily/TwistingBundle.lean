import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.TwistingRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.HomogeneousCoordinates

/-! # Twisting Bundle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A flat closed projective family's canonical homogeneous presentation identifies the restricted ambient twisting bundle with the quotient's O(1). -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n))

theorem Closed.Families.FlatClosedFamily.homogeneousFamilyIso_embedding :
    F.homogeneousFamilyIso.hom ≫ F.inclusion = Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding F.homogeneousIdeal :=
  Closed.EmbeddingKernelIso.closedEmbeddingKernelIso_embedding (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding F.homogeneousIdeal) F.inclusion
    F.homogeneousIdeal_kernel

def Closed.Families.FlatClosedFamily.twistingBundle : Line.Bundles.LineBundle F.scheme.left :=
  (Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).pullback F.inclusion.left

def Closed.Families.FlatClosedFamily.homogeneousTwistingBundleIso :
    (F.twistingBundle.pullback F.homogeneousFamilyIso.hom.left).sheaf ≅
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle F.homogeneousIdeal 1).sheaf := by
  have he : F.homogeneousFamilyIso.hom.left ≫ F.inclusion.left =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion F.homogeneousIdeal := congrArg Over.Hom.left F.homogeneousFamilyIso_embedding
  exact (Scheme.Modules.pullbackComp F.homogeneousFamilyIso.hom.left F.inclusion.left).app
      (Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).sheaf ≪≫
    (Scheme.Modules.pullbackCongr he).app (Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).sheaf ≪≫
    ProjectiveTwisting.TwistingRestriction.affineProjectiveTwistingBundle_quotientIso F.homogeneousIdeal

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
