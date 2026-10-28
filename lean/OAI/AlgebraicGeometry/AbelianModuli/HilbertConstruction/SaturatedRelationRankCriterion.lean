import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SaturationBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.QuotientRankDetection
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyCoordinates

/-! # Saturated Relation Rank Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedRelationRankCriterion

noncomputable section

/-! Above the uniform Hilbert bound, finite flat degree quotients with the prescribed rank already equal their saturated counterparts. -/

open _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}

theorem degreeRelations_eq_saturation_of_flat_rank
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
    (P : Polynomial ℚ) (hP : ∀ p : PrimeSpectrum R,
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
        (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)
    (d : ℕ) (hd : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ d)
    [Module.Flat R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)]
    (hr : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) p =
      (P.eval (d : ℚ)).num.toNat) :
    Homogeneous.IdealIncidence.homogeneousDegreeRelations I d = Homogeneous.IdealIncidence.homogeneousDegreeRelations (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation I) d := by
  let J := HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation I
  have hJ : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal := HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated I
  have : Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J)) := HilbertConstruction.Projective.SaturationBaseChange.projectiveSaturation_flat I
  have hPJ : ∀ p : PrimeSpectrum R,
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
        (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) J)).toIdeal P := by
    intro p
    change HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation I))).toIdeal P
    rw [HilbertConstruction.Projective.SaturationBaseChange.projectiveSaturation_baseChange]
    exact hP p
  have : Module.Finite R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeQuotient_finite I.toIdeal d
  have : Module.Finite R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient J.toIdeal d) := HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeQuotient_finite J.toIdeal d
  have : Module.Projective R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient J.toIdeal d) :=
    (HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformFlatFamilyHilbertGrassmannian J hJ P hPJ d hd).projective_quotient
  apply HilbertConstruction.Flat.QuotientRankDetection.submodule_eq_of_flat_quotient_ranks _ _ (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations_mono (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.le_projectiveSaturation I) d)
  intro p
  exact (hr p).trans (HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree_rankAtStalk J hJ P hPJ d hd p).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedRelationRankCriterion
