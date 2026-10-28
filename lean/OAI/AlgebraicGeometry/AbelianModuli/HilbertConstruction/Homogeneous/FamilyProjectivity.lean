import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.EmbeddingBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products

/-! # Family Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.FamilyProjectivity

noncomputable section

/-! A homogeneous projective quotient has an actual projective presentation over its affine base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def homogeneousProjectiveFamilyPresentation
    {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Projective.ProjectivePresentations.ProjectivePresentation (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I) where
  dimension := n
  embedding := Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding I ≫ (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n).inv
  closedImmersion := by
    have : IsClosedImmersion (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding I).left :=
      inferInstanceAs (IsClosedImmersion (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I))
    have : IsClosedImmersion (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n).inv.left :=
      Grassmann.ProjectivePresentation.overIso_closedImmersion (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n).symm
    change IsClosedImmersion ((Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding I).left ≫
      (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n).inv.left)
    exact IsClosedImmersion.comp _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.FamilyProjectivity
