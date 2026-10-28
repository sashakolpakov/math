import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureFlatness
import Mathlib.Algebra.Module.FinitePresentation

/-! # Valuation Closure Relations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureRelations.GradedHilbert

noncomputable section

/-! Every homogeneous relation degree of a valuation-ring closure is
finitely generated, because its quotient is finite free. -/

universe u
variable {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}

theorem valuationClosure_degreeRelations_fg (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (d : ℕ) :
    (Hilbert.Polynomial.GradedHilbert.degreeRelations (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I).toIdeal d).FG := by
  let J := ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I
  let Q := Hilbert.Polynomial.GradedHilbert.DegreeQuotient J.toIdeal d
  let : Module.Free R Q := ValuationClosureFlatness.GradedHilbert.valuationClosure_degree_free I d
  let : Module.FinitePresentation R Q := Module.finitePresentation_of_projective R Q
  have h := Module.FinitePresentation.fg_ker (Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal d).mkQ
    (Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal d).mkQ_surjective
  rwa [Submodule.ker_mkQ] at h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureRelations.GradedHilbert
