import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.EmbeddingBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.EmbeddingKernelIso

/-! # Projective Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ProjectiveFamilies

noncomputable section

/-! Homogeneous projective quotients over the coefficient base and their embedding-compatible ideal-sheaf isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

instance homogeneousProjectiveEmbedding_closed : IsClosedImmersion (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding I).left :=
  HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion_isClosedImmersion I

def homogeneousProjectiveFamilyIso (J : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    (h : (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I).ker = (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J).ker) :
    Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily J :=
  Closed.EmbeddingKernelIso.closedEmbeddingKernelIso (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding I) (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding J) h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ProjectiveFamilies
