import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.QuotientFlatness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Projective

/-! # Reconstructed Projective Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
Actual proper projective families reconstructed from compatible degree relations.
Flatness of every degree quotient implies flatness of the projective structure
morphism, checked on its standard homogeneous affine charts.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R σ : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (D : GradedIdealReconstruction.GradedIdealRelations R σ)

def GradedIdealReconstruction.GradedIdealRelations.projectiveFamily : Over (Spec (CommRingCat.of R)) :=
  Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientGrading D.toHomogeneousIdeal))

instance GradedIdealReconstruction.GradedIdealRelations.projectiveFamily_proper [Finite σ] : IsProper D.projectiveFamily.hom :=
  HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective.projectiveQuotient_proper D.toHomogeneousIdeal

def GradedIdealReconstruction.GradedIdealRelations.projectiveFamilyEmbedding : D.projectiveFamily ⟶
    Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (MvPolynomial.homogeneousSubmodule σ R)) :=
  Over.homMk (HilbertScheme.Presentations.Homogeneous.ProjectiveQuotient.HomogeneousQuotient.projectiveQuotientInclusion D.toHomogeneousIdeal)
    (HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective.projectiveQuotientInclusion_over D.toHomogeneousIdeal)

instance GradedIdealReconstruction.GradedIdealRelations.projectiveFamilyEmbedding_closed : IsClosedImmersion D.projectiveFamilyEmbedding.left :=
  HilbertScheme.Presentations.Homogeneous.ProjectiveQuotient.HomogeneousQuotient.projectiveQuotientInclusion_isClosedImmersion D.toHomogeneousIdeal

theorem GradedIdealReconstruction.GradedIdealRelations.quotientDegree_flat
    (h : ∀ d, Module.Flat R (MvPolynomial.homogeneousSubmodule σ R d ⧸ D.piece d)) (d : ℕ) :
    Module.Flat R (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientGrading D.toHomogeneousIdeal d) := by
  have hd : Module.Flat R (MvPolynomial.homogeneousSubmodule σ R d ⧸
      Homogeneous.IdealIncidence.homogeneousDegreeRelations D.toHomogeneousIdeal d) := by
    rw [D.toHomogeneousIdeal_degree]
    exact h d
  exact (Module.Flat.equiv_iff (Homogeneous.QuotientFlatness.homogeneousDegreeQuotientEquiv D.toHomogeneousIdeal d)).mp hd

theorem GradedIdealReconstruction.GradedIdealRelations.projectiveFamily_flat
    (h : ∀ d, Module.Flat R (MvPolynomial.homogeneousSubmodule σ R d ⧸ D.piece d)) :
    Flat D.projectiveFamily.hom := by
  exact HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap_flat
    (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientGrading D.toHomogeneousIdeal)
    (fun i : σ => HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap D.toHomogeneousIdeal (MvPolynomial.X i))
    (fun i => (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap D.toHomogeneousIdeal).map_mem
      (MvPolynomial.isHomogeneous_X R i))
    (HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective.quotient_irrelevant_le_span_variables D.toHomogeneousIdeal)
    0 (fun d _ => D.quotientDegree_flat h d)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
