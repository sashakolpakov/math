import OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeGeneratedIdeal
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial

/-! # Field Function Generation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FieldFunctionGeneration.GradedHilbert

noncomputable section

/-! A field ideal whose Hilbert function already equals the prescribed
polynomial in the uniform range is generated there by a single degree.
The ideal need not be saturated. -/

universe u
variable {K : Type u} [Field K] {n : ℕ}

theorem field_degreeGenerated_relations_of_hilbertFunction
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (P : Polynomial ℚ) (N : ℕ)
    (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N)
    (hF : ∀ d ≥ N, (Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d : ℚ) = P.eval (d : ℚ)) (d : ℕ) (hd : N ≤ d) :
    Hilbert.Polynomial.GradedHilbert.degreeRelations (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N).toIdeal d = Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d := by
  let J := Projective.Saturation.GradedHilbert.projectiveSaturation I
  have hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial J.toIdeal P :=
    (Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff I P).mpr ⟨N, hF⟩
  have hJ := Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec n P K J (Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated I) hP
  have hrel (e : ℕ) (he : N ≤ e) : Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal e = Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal e := by
    apply Hilbert.Polynomial.GradedHilbert.degreeRelations_eq_of_le_of_hilbertFunction_eq (Projective.Saturation.GradedHilbert.le_projectiveSaturation I) e
    exact_mod_cast (hF e he).trans (hJ.2 e (hN.trans he)).symm
  rw [DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal_eq_of_degreeRelations_eq I J N (hrel N le_rfl)]
  obtain ⟨B, hB, hBdeg⟩ := hJ.1
  rw [DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal_eventual_relations J N B hB (fun b hb => by
    obtain ⟨_, e, he, hbe⟩ := hBdeg b hb
    exact ⟨e, he.trans hN, hbe⟩) d hd]
  exact (hrel d hd).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FieldFunctionGeneration.GradedHilbert
