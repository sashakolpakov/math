import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.EndomorphismClosedLocus
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RepresentedProjectiveEquationLocus

/-! # Endomorphism Equation Package -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.EndomorphismEquationPackage.Core

noncomputable section

/-! Assemble the statement's complete endomorphism/equation package
when the supplied equation sources have projective presentations. The general
proper-source assertion is separate from this proved projective-source case. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable (A : Over S) [GrpObj A]
variable [Flat A.hom] [IsProper A.hom] [LocallyOfFinitePresentation A.hom]
variable {B : Has.Core.ProjectivePresentation (A ⨯ A)} {n : ℕ} {P : Fin n → Polynomial ℚ}

theorem endomorphismEquationLoci_of_projective_sources
    (BA : Has.Core.ProjectivePresentation A) (L : Loci.Core.HilbertHomLoci A A B n P)
    (R : Endomorphisms.Core.FiniteEndomorphismEquations A n)
    (hR : ∀ r ∈ R, Nonempty (Has.Core.ProjectivePresentation r.source)) :
    Nonempty (Loci.Core.EndomorphismEquationLoci A B n P L R) := by
  obtain ⟨E, j, hj, e, he⟩ := L.endomorphism_closed_locus A BA
  let : IsClosedImmersion j.left := hj
  let : LocallyOfFiniteType L.homScheme.hom := L.hom_finiteType
  let : IsLocallyNoetherian L.homScheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian L.homScheme.hom
  let : IsLocallyNoetherian E.left := LocallyOfFiniteType.isLocallyNoetherian j.left
  obtain ⟨Z, k, hk, e', he'⟩ := RepresentedProjectiveEquationLocus.Core.represented_projective_equation_locus
    (EndomorphismPolynomialSubfunctors.Core.endomorphismPolynomialSubfunctor A n B P) e R hR
  exact ⟨{
    endScheme := E
    solutionScheme := Z
    endLocus := EndomorphismPolynomialSubfunctors.Core.endomorphismPolynomialSubfunctor A n B P
    solutionLocus := EndomorphismPolynomialSubfunctors.Core.endomorphismPolynomialSolutionSubfunctor A n B P R
    end_mem := fun _ _ => Iff.rfl
    solution_mem := fun _ _ => Iff.rfl
    endEquivalence := e
    solutionEquivalence := e'
    forgetGroup := j
    forgetEquations := k
    group_closed := hj
    equations_closed := hk
    group_compatibility := he
    equations_compatibility := he' }⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.EndomorphismEquationPackage.Core
