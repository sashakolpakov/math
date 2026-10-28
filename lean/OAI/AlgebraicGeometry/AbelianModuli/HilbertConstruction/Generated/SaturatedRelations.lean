import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeneratedCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedRelationRankCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.FinitePersistence

/-! # Saturated Relations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The retained high-degree relations on the generated parameter locus agree with their saturated coordinate relations. -/

open _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n B N : ℕ} {P : Polynomial ℚ}
variable (D : Truncated.GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N))

theorem Truncated.GradedClassification.TruncatedGradedQuotientData.generated_saturated_retained_relations
    (hgen : D.GeneratedFromDegree N) (hB : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B)
    (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hP : ∀ p : PrimeSpectrum R,
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
        (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) D.generatedIdeal)).toIdeal P)
    (d : Fin (B + 1)) (hd : N ≤ d.val) :
    (D.quotient d).toSubmodule = Homogeneous.IdealIncidence.homogeneousDegreeRelations (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation D.generatedIdeal) d := by
  have : Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading D.generatedIdeal)) :=
    D.projectiveFamily_flat_of_generatedFromDegree N hB hgen
  have : Module.Projective R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient D.generatedIdeal.toIdeal d) :=
    D.retainedDegreeQuotient_projective d
  rw [← D.generatedIdeal_degree d]
  apply SaturatedRelationRankCriterion.degreeRelations_eq_saturation_of_flat_rank D.generatedIdeal P hP d (hN.trans hd)
  intro p
  change Module.rankAtStalk (R := R)
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d ⧸ Homogeneous.IdealIncidence.homogeneousDegreeRelations D.generatedIdeal d) p = _
  rw [D.generatedIdeal_degree d]
  have hr := (D.quotient d).rankAtStalk_eq p
  have hrd : Uniform.GeneratedCoordinates.generatedHilbertRanks n P N d.val = (P.eval (d.val : ℚ)).num.toNat :=
    ite_eq_right (Nat.not_lt.mpr hd)
  exact hr.trans hrd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
