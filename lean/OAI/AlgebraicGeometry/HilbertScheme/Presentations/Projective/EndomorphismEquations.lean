import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ProjectiveEquationLoci
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EndomorphismTupleEquations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ExactSegrePresentation

/-! # Endomorphism Equations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.EndomorphismEquations.Core

noncomputable section

/-! Every source in the finite group-law equation list has a projective
presentation, obtained from the given presentation by the Segre construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (A : Over S) [GrpObj A]
variable [Flat A.hom] [IsProper A.hom] [LocallyOfFinitePresentation A.hom]
variable (BA : Has.Core.ProjectivePresentation A) (n : ℕ)

include BA in
theorem endomorphismTupleEquations_projective_sources :
    ∀ r ∈ EndomorphismTupleEquations.Core.endomorphismTupleEquations A n, Nonempty (Has.Core.ProjectivePresentation r.source) := by
  intro r hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  exact ⟨Relative.SegrePresentation.Core.segreProductPresentation BA BA⟩

include BA in
theorem endomorphismTuples_closed_lifts
    {M : Over S} [IsLocallyNoetherian M.left]
    (φ : yoneda.obj M ⟶ Has.Core.morphismTuples A A n) :
    ∃ (Z : Over S) (j : Z ⟶ M), IsClosedImmersion j.left ∧
      ∀ (T : Over S) (x : T ⟶ M),
        (∀ i, Endomorphisms.Core.PreservesGroupLaw A (φ.app (.op T) x i)) ↔
          ∃! y : T ⟶ Z, y ≫ j = x := by
  obtain ⟨Z, j, hj, htest⟩ := Finite.ProjectiveEquationLoci.Core.finite_projective_equations_closed_lifts
    (EndomorphismTupleEquations.Core.endomorphismTupleEquations A n) (endomorphismTupleEquations_projective_sources A BA n) φ
  refine ⟨Z, j, hj, ?_⟩
  intro T x
  exact (EndomorphismTupleEquations.Core.satisfies_endomorphismTupleEquations_iff A n _).symm.trans (htest T x)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.EndomorphismEquations.Core
