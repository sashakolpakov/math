import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.EndomorphismClosedLocus
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RepresentedProperEquationLocus

/-! # Endomorphism Equation Package -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.EndomorphismEquationPackage.Core

noncomputable section

/-! The full endomorphism/equation package for arbitrary finite systems
of natural equations with proper flat sources. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable (A : Over S) [GrpObj A]
variable [Flat A.hom] [IsProper A.hom] [LocallyOfFinitePresentation A.hom]
variable {B : Has.Core.ProjectivePresentation (A ⨯ A)} {n : ℕ} {P : Fin n → Polynomial ℚ}

theorem endomorphismEquationLoci_of_proper_sources
    (BA : Has.Core.ProjectivePresentation A) (L : Loci.Core.HilbertHomLoci A A B n P)
    (R : Endomorphisms.Core.FiniteEndomorphismEquations A n) :
    Nonempty (Loci.Core.EndomorphismEquationLoci A B n P L R) := by
  obtain ⟨E, j, hj, e, he⟩ := L.endomorphism_closed_locus A BA
  let : IsClosedImmersion j.left := hj
  let : LocallyOfFiniteType L.homScheme.hom := L.hom_finiteType
  let : IsLocallyNoetherian L.homScheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian L.homScheme.hom
  let : IsLocallyNoetherian E.left := LocallyOfFiniteType.isLocallyNoetherian j.left
  obtain ⟨Z, k, hk, e', he'⟩ := RepresentedProperEquationLocus.Core.represented_proper_equation_locus
    (EndomorphismPolynomialSubfunctors.Core.endomorphismPolynomialSubfunctor A n B P) e R
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

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.EndomorphismEquationPackage.Core
