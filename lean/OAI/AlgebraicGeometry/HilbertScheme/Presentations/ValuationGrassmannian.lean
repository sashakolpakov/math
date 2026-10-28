import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureGeneration
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.LinearTransport

/-! # Valuation Grassmannian -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationGrassmannian.GradedHilbert

noncomputable section

/-! Uniform Grassmannian coordinates for valuation closures, with ranks
computed from the actual Hilbert polynomial of the generic ideal. -/

universe u
variable {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
variable (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P)

include hI hP in
theorem valuationClosure_rankAtStalk (d : ℕ) (hd : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ d) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I).toIdeal d) p =
      (P.eval (d : ℚ)).num.toNat := by
  let := ValuationClosureFlatness.GradedHilbert.valuationClosure_degree_free (R := R) I d
  rw [Module.rankAtStalk_eq_finrank_of_free]
  have hK := ValuationClosureFunction.GradedHilbert.degreeQuotient_finrank_baseChange_of_free (L := K) (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I) d
  rw [ContractedIdealLocalization.GradedHilbert.contractedHomogeneousIdeal_localization (nonZeroDivisors R) I] at hK
  change Hilbert.Polynomial.GradedHilbert.hilbertFunction (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I).toIdeal d = _
  rw [← hK]
  have h := (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec n P K I hI hP).2 d hd
  rw [← h]
  simp only [Rat.num_natCast, Int.toNat_natCast]

def valuationHilbertGrassmannian (d : ℕ) (hd : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ d) :
    Module.Grassmannian R (Hilbert.Polynomial.GradedHilbert.grading R n d) (P.eval (d : ℚ)).num.toNat where
  toSubmodule := Hilbert.Polynomial.GradedHilbert.degreeRelations (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I).toIdeal d
  finite_quotient := inferInstance
  projective_quotient := by
    let := ValuationClosureFlatness.GradedHilbert.valuationClosure_degree_free (R := R) I d
    infer_instance
  rankAtStalk_eq := valuationClosure_rankAtStalk I hI P hP d hd

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationGrassmannian.GradedHilbert
