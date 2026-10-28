import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.TupleSubfunctors
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Endomorphisms

/-! # Endomorphism Polynomial Subfunctors -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.EndomorphismPolynomialSubfunctors.Core

noncomputable section

/-! The exact polynomial-restricted endomorphism and equation-solution
subfunctors required in the Presentations conclusion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (A : Over S) [GrpObj A]
variable [Flat A.hom] [IsProper A.hom] [LocallyOfFinitePresentation A.hom]
variable (n : ℕ) (B : Has.Core.ProjectivePresentation (A ⨯ A)) (P : Fin n → Polynomial ℚ)

def endomorphismPolynomialSubfunctor : Subfunctor (Endomorphisms.Core.endomorphismTuples A n) :=
  (Presentations.Polynomial.TupleSubfunctors.Core.morphismPolynomialTupleSubfunctor A A n B P).preimage (Endomorphisms.Core.forgetGroupLaw A n)

theorem endomorphismPolynomialSubfunctor_mem {T : Over S}
    (f : (Endomorphisms.Core.endomorphismTuples A n).obj (.op T)) :
    f ∈ (endomorphismPolynomialSubfunctor A n B P).obj (.op T) ↔
      Has.Core.HasGraphPolynomials A A n B P ((Endomorphisms.Core.forgetGroupLaw A n).app (.op T) f) := Iff.rfl

def endomorphismPolynomialSolutionSubfunctor (R : Endomorphisms.Core.FiniteEndomorphismEquations A n) :
    Subfunctor (Endomorphisms.Core.endomorphismTuples A n) :=
  endomorphismPolynomialSubfunctor A n B P ⊓ Endomorphisms.Core.solutionSubfunctor R

theorem endomorphismPolynomialSolutionSubfunctor_mem (R : Endomorphisms.Core.FiniteEndomorphismEquations A n)
    {T : Over S} (f : (Endomorphisms.Core.endomorphismTuples A n).obj (.op T)) :
    f ∈ (endomorphismPolynomialSolutionSubfunctor A n B P R).obj (.op T) ↔
      Has.Core.HasGraphPolynomials A A n B P ((Endomorphisms.Core.forgetGroupLaw A n).app (.op T) f) ∧
        Endomorphisms.Core.SatisfiesEquations R f := Iff.rfl

def polynomialEndomorphismForgetGroup : (endomorphismPolynomialSubfunctor A n B P).toFunctor ⟶
    (Presentations.Polynomial.TupleSubfunctors.Core.morphismPolynomialTupleSubfunctor A A n B P).toFunctor :=
  (Presentations.Polynomial.TupleSubfunctors.Core.morphismPolynomialTupleSubfunctor A A n B P).fromPreimage (Endomorphisms.Core.forgetGroupLaw A n)

theorem polynomialEndomorphismForgetGroup_inclusion :
    polynomialEndomorphismForgetGroup A n B P ≫ (Presentations.Polynomial.TupleSubfunctors.Core.morphismPolynomialTupleSubfunctor A A n B P).ι =
      (endomorphismPolynomialSubfunctor A n B P).ι ≫ Endomorphisms.Core.forgetGroupLaw A n := rfl

def polynomialSolutionForgetEquations (R : Endomorphisms.Core.FiniteEndomorphismEquations A n) :
    (endomorphismPolynomialSolutionSubfunctor A n B P R).toFunctor ⟶
      (endomorphismPolynomialSubfunctor A n B P).toFunctor where
  app _T := ↾fun f => ⟨f.val, f.property.1⟩
  naturality _T _U _a := rfl

theorem polynomialSolutionForgetEquations_inclusion (R : Endomorphisms.Core.FiniteEndomorphismEquations A n) :
    polynomialSolutionForgetEquations A n B P R ≫ (endomorphismPolynomialSubfunctor A n B P).ι =
      (endomorphismPolynomialSolutionSubfunctor A n B P R).ι := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.EndomorphismPolynomialSubfunctors.Core
