import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureGeneration
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedTailGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.QuotientFinitePresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Properness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.BaseChange

/-! # Valuation Closure Finite Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureFinitePresentation.GradedHilbert

noncomputable section

/-! The actual closure of a saturated projective fraction-field ideal is
finitely presented over an arbitrary valuation ring. Together with flatness,
this gives an unconditional projective family extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped nonZeroDivisors

universe u
variable {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)

include hI in
theorem valuationClosure_ideal_fg : (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I).toIdeal.FG := by
  obtain ⟨P, hP⟩ := Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial I
  let N := Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P
  apply Finite.GradedTailGeneration.GradedHilbert.homogeneousIdeal_fg_of_finite_tail_generation _ N
  · exact fun d _ => ValuationClosureRelations.GradedHilbert.valuationClosure_degreeRelations_fg I d
  · exact ValuationClosureGeneration.GradedHilbert.valuationClosure_degreeGenerated_relations I hI P hP N le_rfl

include hI in
theorem valuationClosure_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (Projective.Flatness.GradedHilbert.projectiveStructureMap
      (Graded.Quotient.GradedHilbert.quotientGrading (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I))) :=
  AbelianModuli.HilbertConstruction.Projective.QuotientFinitePresentation.projectiveQuotient_locallyFinitePresentation _ (valuationClosure_ideal_fg I hI)

include hI in
theorem valuation_projective_family_extension :
    ∃ J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n), Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal ∧ J.toIdeal.FG ∧
      Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J)) ∧
      IsProper (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J)) ∧
      LocallyOfFinitePresentation (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J)) ∧
      Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) J = I ∧
      ∃ q : Projective.Quotient.GradedHilbert.projectiveQuotient I ⟶ Projective.Quotient.GradedHilbert.projectiveQuotient J,
        IsPullback q (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))
          (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J))
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  let J := ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I
  have hJ : Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) J = I := ContractedIdealLocalization.GradedHilbert.contractedHomogeneousIdeal_localization R⁰ I
  refine ⟨J, ContractedIdealSaturation.GradedHilbert.contractedHomogeneousIdeal_saturated I hI, valuationClosure_ideal_fg I hI,
    ValuationClosureFlatness.GradedHilbert.valuationClosure_projective_flat I, Projective.Properness.GradedHilbert.projectiveQuotient_proper J,
    valuationClosure_locallyOfFinitePresentation I hI, hJ, ?_⟩
  have hp : ∃ q : Projective.Quotient.GradedHilbert.projectiveQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) J) ⟶ Projective.Quotient.GradedHilbert.projectiveQuotient J,
      IsPullback q (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) J)))
        (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J))
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    ⟨Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap J, Projective.BaseChange.GradedHilbert.projectiveQuotient_isPullback J⟩
  rwa [hJ] at hp

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureFinitePresentation.GradedHilbert
