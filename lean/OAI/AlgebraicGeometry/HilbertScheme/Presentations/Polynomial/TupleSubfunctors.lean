import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.PolynomialSubfunctor
import Mathlib.CategoryTheory.Subfunctor.Image

/-! # Tuple Subfunctors -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.TupleSubfunctors.Core

noncomputable section

/-! Exact finite-tuple polynomial subfunctors for the Hilbert and Hom
functors in the Presentations statement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X Y : Over S) (n : ℕ)
variable (B : Has.Core.ProjectivePresentation (X ⨯ Y)) (P : Fin n → Polynomial ℚ)

def hilbertPolynomialTupleSubfunctor : Subfunctor (Has.Core.hilbertTuples X Y n) where
  obj _T := {I | Has.Core.HasHilbertPolynomials X Y n B P I}
  map a I h i := FiberPolynomialBaseChange.Core.hasFiberHilbertPolynomial_pullback B a.unop (I i) (P i) (h i)

theorem hilbertPolynomialTupleSubfunctor_mem {T : Over S}
    (I : (Has.Core.hilbertTuples X Y n).obj (.op T)) :
    I ∈ (hilbertPolynomialTupleSubfunctor X Y n B P).obj (.op T) ↔ Has.Core.HasHilbertPolynomials X Y n B P I := Iff.rfl

variable [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated Y.hom]

def morphismPolynomialTupleSubfunctor : Subfunctor (Has.Core.morphismTuples X Y n) :=
  (hilbertPolynomialTupleSubfunctor X Y n B P).preimage (Has.Core.graphs X Y n)

theorem morphismPolynomialTupleSubfunctor_mem {T : Over S}
    (f : (Has.Core.morphismTuples X Y n).obj (.op T)) :
    f ∈ (morphismPolynomialTupleSubfunctor X Y n B P).obj (.op T) ↔ Has.Core.HasGraphPolynomials X Y n B P f := Iff.rfl

def polynomialGraphs : (morphismPolynomialTupleSubfunctor X Y n B P).toFunctor ⟶
    (hilbertPolynomialTupleSubfunctor X Y n B P).toFunctor :=
  (hilbertPolynomialTupleSubfunctor X Y n B P).fromPreimage (Has.Core.graphs X Y n)

theorem polynomialGraphs_inclusion :
    polynomialGraphs X Y n B P ≫ (hilbertPolynomialTupleSubfunctor X Y n B P).ι =
      (morphismPolynomialTupleSubfunctor X Y n B P).ι ≫ Has.Core.graphs X Y n := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.TupleSubfunctors.Core
