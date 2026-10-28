import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ProjectiveFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.TwistingRestriction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealEquivalence

/-! # Projective Homogeneous Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding

noncomputable section

/-! Every closed projective embedding has a homogeneous presentation that identifies its actual restricted twisting bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealEquivalence.GradedHilbert

universe u

variable {R : Type u} [CommRing R] {n : ℕ} {X : Over (Spec (.of R))}
variable (i : X ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R n) [IsClosedImmersion i.left]

def ideal : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) := HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf i.left.ker

def presentation : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (ideal i) ≅ X :=
  EmbeddingKernelIso.closedEmbeddingKernelIso (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding (ideal i)) i
    (HilbertScheme.Presentations.Projective.IdealEquivalence.GradedHilbert.projectiveQuotient_homogeneousIdealOfSheaf i.left.ker)

theorem presentation_embedding :
    (presentation i).hom.left ≫ i.left = HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (ideal i) :=
  congrArg Over.Hom.left (EmbeddingKernelIso.closedEmbeddingKernelIso_embedding
    (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding (ideal i)) i
    (HilbertScheme.Presentations.Projective.IdealEquivalence.GradedHilbert.projectiveQuotient_homogeneousIdealOfSheaf i.left.ker))

def twistingIso :
    (((Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).pullback i.left).pullback
      (presentation i).hom.left).sheaf ≅ (ProjectiveTwisting.Bundle.projectiveTwistingBundle (ideal i) 1).sheaf :=
  (Scheme.Modules.pullbackComp (presentation i).hom.left i.left).app
    (Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).sheaf ≪≫
  (Scheme.Modules.pullbackCongr (presentation_embedding i)).app
    (Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).sheaf ≪≫
  ProjectiveTwisting.TwistingRestriction.affineProjectiveTwistingBundle_quotientIso (ideal i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding
