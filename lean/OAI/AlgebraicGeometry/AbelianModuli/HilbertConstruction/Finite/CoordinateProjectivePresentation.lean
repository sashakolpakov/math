import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Coordinate Projective Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoordinateProjectivePresentation

noncomputable section

/-! Convert a closed immersion in polynomial projective space into an HilbertConstruction presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R σ : Type u) [CommRing R] [Fintype σ] [Nonempty σ]

def finiteCoordinateProjectiveSpaceIso :
    Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R)) ≅
      Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of R)) (Fintype.card σ - 1) :=
  Projective.SpaceReindex.affineProjectiveSpaceReindexIso R (Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv σ) ≪≫
    (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) (Fintype.card σ - 1)).symm

variable {R σ}
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
variable (j : X ⟶ Proj (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R))
variable (hj : j ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) = f)

def finiteCoordinateProjectiveEmbedding :
    Over.mk f ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of R)) (Fintype.card σ - 1) :=
  (Over.homMk j hj : Over.mk f ⟶ Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R))) ≫
    (finiteCoordinateProjectiveSpaceIso R σ).hom

theorem finiteCoordinateProjectiveEmbedding_closed [IsClosedImmersion j] :
    IsClosedImmersion (finiteCoordinateProjectiveEmbedding f j hj).left := by
  change IsClosedImmersion (j ≫ (finiteCoordinateProjectiveSpaceIso R σ).hom.left)
  have : IsClosedImmersion (finiteCoordinateProjectiveSpaceIso R σ).hom.left :=
    Grassmann.ProjectivePresentation.overIso_closedImmersion (finiteCoordinateProjectiveSpaceIso R σ)
  infer_instance

def finiteCoordinateProjectivePresentation [IsClosedImmersion j] :
    Projective.ProjectivePresentations.ProjectivePresentation (Over.mk f) where
  dimension := Fintype.card σ - 1
  embedding := finiteCoordinateProjectiveEmbedding f j hj
  closedImmersion := finiteCoordinateProjectiveEmbedding_closed f j hj

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoordinateProjectivePresentation
