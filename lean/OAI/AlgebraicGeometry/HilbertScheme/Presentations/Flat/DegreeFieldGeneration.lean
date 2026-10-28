import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.RelationFiberEquality
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FieldFunctionGeneration
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeGeneratedBaseChange

/-! # Degree Field Generation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.DegreeFieldGeneration.GradedHilbert

noncomputable section

/-! Uniform generation over arbitrary rings follows from finite relations,
flat degree quotients, and the actual residue-field Hilbert functions. -/

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

theorem degreeGenerated_relations_of_flat_field_hilbertFunction
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (P : Polynomial ℚ) (N : ℕ)
    (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N)
    (hF : ∀ p : PrimeSpectrum R, ∀ e ≥ N,
      (Hilbert.Polynomial.GradedHilbert.hilbertFunction (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I).toIdeal e : ℚ) =
        P.eval (e : ℚ))
    (d : ℕ) (hd : N ≤ d) [Module.Finite R (Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d)]
    [Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)] :
    Hilbert.Polynomial.GradedHilbert.degreeRelations (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N).toIdeal d = Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d := by
  apply Presentations.Finite.RelationFiberEquality.finite_relation_eq_of_residue_baseChange R _ _
    (Hilbert.Polynomial.GradedHilbert.degreeRelations_mono (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal_le I N) d)
  intro p
  apply Submodule.map_injective_of_injective
    (Homogeneous.CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv (R := R) (S := p.asIdeal.ResidueField) (n := n) d).injective
  rw [RelationsBaseChangeMap.GradedHilbert.degreeRelations_baseChange_map, RelationsBaseChangeMap.GradedHilbert.degreeRelations_baseChange_map, DegreeGeneratedBaseChange.GradedHilbert.degreeGeneratedIdeal_baseChange]
  exact FieldFunctionGeneration.GradedHilbert.field_degreeGenerated_relations_of_hilbertFunction _ P N hN (hF p) d hd

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.DegreeFieldGeneration.GradedHilbert
