import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberPolynomialBaseChange

/-! # Polynomial Subfunctor -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.PolynomialSubfunctor.Core

noncomputable section

/-! The exact polynomial condition defines a subfunctor of the native
Hilbert-family functor on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X : Over S} (B : Has.Core.ProjectivePresentation X) (P : Polynomial ℚ)

def hilbertPolynomialSubfunctor : Subfunctor (Functor.familyFunctor X) where
  obj _T := {I | Has.Core.HasFiberHilbertPolynomial B I P}
  map f I h := FiberPolynomialBaseChange.Core.hasFiberHilbertPolynomial_pullback B f.unop I P h

theorem hilbertPolynomialSubfunctor_mem {T : Over S} (I : Functor.Family X T) :
    I ∈ (hilbertPolynomialSubfunctor B P).obj (.op T) ↔ Has.Core.HasFiberHilbertPolynomial B I P := Iff.rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.PolynomialSubfunctor.Core
