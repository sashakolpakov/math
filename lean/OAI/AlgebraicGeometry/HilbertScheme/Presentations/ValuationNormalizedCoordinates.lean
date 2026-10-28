import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationGrassmannian
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.DegreeIdealPresentation

/-! # Valuation Normalized Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationNormalizedCoordinates.GradedHilbert

noncomputable section

/-! Normalized finite equations for a valuation closure, with every high
degree quotient free and of the exact polynomial rank. -/

universe u
variable {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
variable (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P)

theorem valuationClosure_hilbertFunction (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.hilbertFunction (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I).toIdeal d = Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d := by
  let := ValuationClosureFlatness.GradedHilbert.valuationClosure_degree_free (R := R) I d
  have h := ValuationClosureFunction.GradedHilbert.degreeQuotient_finrank_baseChange_of_free (L := K) (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I) d
  rw [ContractedIdealLocalization.GradedHilbert.contractedHomogeneousIdeal_localization (nonZeroDivisors R) I] at h
  exact h.symm

include hI hP in
theorem exists_valuation_normalized_hilbert_coordinates (N : ℕ)
    (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃ (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R),
      Normalized.Matrices.Grassmannian.IsNormalized a Q ∧ Function.Injective a ∧
      Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q = DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I) N ∧
      Projective.Saturation.GradedHilbert.projectiveSaturation (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q) = ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I ∧
      ∀ d ≥ N, Module.Free R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).toIdeal d) ∧
        (Hilbert.Polynomial.GradedHilbert.hilbertFunction (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).toIdeal d : ℚ) = P.eval (d : ℚ) := by
  let J := ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I
  let H : Module.Grassmannian R (Hilbert.Polynomial.GradedHilbert.grading R n N) (Fintype.card ι) := {
    toSubmodule := Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal N
    finite_quotient := inferInstance
    projective_quotient := by
      let := ValuationClosureFlatness.GradedHilbert.valuationClosure_degree_free (R := R) I N
      infer_instance
    rankAtStalk_eq := fun p => (ValuationGrassmannian.GradedHilbert.valuationClosure_rankAtStalk I hI P hP N hN p).trans hr.symm }
  obtain ⟨a, Q, hQ, ha, he⟩ := Normalized.DegreeIdealPresentation.GradedHilbert.exists_normalized_degreeIdeal_presentation J H rfl
  refine ⟨a, Q, hQ, ha, he, ?_, ?_⟩
  · rw [he]
    exact (ValuationClosureGeneration.GradedHilbert.valuationClosure_finite_equations I hI P hP N hN).2
  · intro d hd
    have hrel : Hilbert.Polynomial.GradedHilbert.degreeRelations (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).toIdeal d = Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal d := by
      rw [he]
      exact ValuationClosureGeneration.GradedHilbert.valuationClosure_degreeGenerated_relations I hI P hP N hN d hd
    let := ValuationClosureFlatness.GradedHilbert.valuationClosure_degree_free (R := R) I d
    refine ⟨Module.Free.of_equiv (Submodule.quotEquivOfEq _ _ hrel.symm), ?_⟩
    have hdim : Hilbert.Polynomial.GradedHilbert.hilbertFunction (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).toIdeal d = Hilbert.Polynomial.GradedHilbert.hilbertFunction J.toIdeal d :=
      (Submodule.quotEquivOfEq _ _ hrel).finrank_eq
    rw [hdim, valuationClosure_hilbertFunction I d]
    exact (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec n P K I hI hP).2 d (hN.trans hd)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationNormalizedCoordinates.GradedHilbert
