import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureFunction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureRelations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ContractedIdealSaturation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.DegreeFieldGeneration
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.DegreeGeneratedIdeal
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SaturatedTailReconstruction

/-! # Valuation Closure Generation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureGeneration.GradedHilbert

noncomputable section

/-! Uniform single-degree equations recover the actual valuation-ring
closure of a saturated field ideal, without noetherianity of the valuation ring. -/

universe u
variable {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
variable (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P)
include hI hP

theorem valuationClosure_degreeGenerated_relations (N : ℕ) (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N)
    (d : ℕ) (hd : N ≤ d) :
    Hilbert.Polynomial.GradedHilbert.degreeRelations (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I) N).toIdeal d =
      Hilbert.Polynomial.GradedHilbert.degreeRelations (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I).toIdeal d := by
  let J := ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I
  let : Module.Finite R (Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal d) :=
    Module.Finite.of_fg (ValuationClosureRelations.GradedHilbert.valuationClosure_degreeRelations_fg I d)
  let : Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient J.toIdeal d) := ValuationClosureFlatness.GradedHilbert.valuationClosure_degree_flat I d
  apply Presentations.Flat.DegreeFieldGeneration.GradedHilbert.degreeGenerated_relations_of_flat_field_hilbertFunction J P N hN _ d hd
  intro p e he
  rw [ValuationClosureFunction.GradedHilbert.valuationClosure_hilbertFunction_baseChange I p.asIdeal.ResidueField e]
  exact (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec n P K I hI hP).2 e (hN.trans he)

theorem valuationClosure_finite_equations (N : ℕ) (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N) :
    (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I) N).toIdeal.FG ∧
      Projective.Saturation.GradedHilbert.projectiveSaturation (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I) N) =
        ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I := by
  refine ⟨Presentations.Finite.DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal_fg _ N (ValuationClosureRelations.GradedHilbert.valuationClosure_degreeRelations_fg I N), ?_⟩
  exact SaturatedTailReconstruction.GradedHilbert.projectiveSaturation_eq_of_le_eventual_relations _ _ (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal_le _ N)
    (ContractedIdealSaturation.GradedHilbert.contractedHomogeneousIdeal_saturated I hI) N (valuationClosure_degreeGenerated_relations I hI P hP N hN)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureGeneration.GradedHilbert
