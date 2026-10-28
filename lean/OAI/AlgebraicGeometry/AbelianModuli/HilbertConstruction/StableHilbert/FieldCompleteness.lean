import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LinearCompleteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.PolynomialSectionEvaluation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.DegreeRank

/-! # Field Completeness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FieldCompleteness.StableHilbertCoverage

noncomputable section

/-! A projective family containing the normalized coordinate frame has
independent degree-one sections. For the original uniform graph power,
its known section rank makes this actual section map an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.DegreeRank.GradedHilbert
universe u
variable {K : Type u} [Field K] {n : ℕ}
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K n))
variable (x : Fin (n + 1) → (Spec (.of K) ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
variable (hx : ∀ i, x i ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I =
  AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of K) K (Pi.single i 1) i (Pi.single_eq_same i 1))

include hx

theorem linearSections_injective_of_frame :
    Function.Injective (SaturatedPolynomialSectionMap.homogeneousPolynomialTwistingSectionMap I 1) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  apply LinearCompleteness.StableHilbertCoverage.linearPolynomial_eq_zero_of_frame_values p
  intro i
  have hs : Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection I 1
      ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal 1).mkQ p) = 0 := by
    change SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I 1 ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal 1).mkQ p) = 0 at hp
    change (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv
      (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).sheaf).symm
        (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I 1 ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal 1).mkQ p)) = 0
    rw [hp]
    exact map_zero _
  apply (Normalized.PolynomialSectionEvaluation.polynomialSection_pullback_zero_iff_normalized_evaluation I p (x i)
    (Pi.single i 1) i (Pi.single_eq_same i 1) (hx i)).mp
  rw [hs, ZeroSections.pullbackSection_zero]

theorem linearSections_bijective_of_frame_rank
    [Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).sheaf)]
    (hr : Module.finrank K
      ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj
        (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).sheaf) = n + 1) :
    Function.Bijective (SaturatedPolynomialSectionMap.homogeneousPolynomialTwistingSectionMap I 1) := by
  have hinj := linearSections_injective_of_frame I x hx
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  rw [hr, HilbertScheme.Presentations.Homogeneous.DegreeRank.GradedHilbert.homogeneousDegree_finrank]
  simp [Nat.add_comm]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FieldCompleteness.StableHilbertCoverage
