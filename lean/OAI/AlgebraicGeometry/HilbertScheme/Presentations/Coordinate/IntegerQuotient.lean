import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerGradedQuotient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Quotient

/-! # Integer Quotient -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert

noncomputable section

/-! Integer grading on the existing homogeneous coordinate quotients. -/

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

def integerIdeal (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    HomogeneousIdeal (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := Fin (n + 1)) R) where
  __ := I.toIdeal
  is_homogeneous' := IntegerPolynomialGrading.GradedModules.ideal_integer_homogeneous R I.toIdeal I.isHomogeneous

def integerQuotientGrading (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    ℤ → Submodule R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) :=
  IntegerGradedQuotient.GradedModules.IntegerQuotient.grading (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) (integerIdeal I)

instance integerQuotientDecomposition (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    DirectSum.Decomposition (integerQuotientGrading I) :=
  IntegerGradedQuotient.GradedModules.IntegerQuotient.quotientDecomposition _ _

instance integerQuotientGradedAlgebra (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    GradedAlgebra (integerQuotientGrading I) := IntegerGradedQuotient.GradedModules.IntegerQuotient.quotientGradedAlgebra _ _

instance integerQuotientGradedSMul (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := Fin (n + 1)) R) (integerQuotientGrading I) :=
  IntegerGradedQuotient.GradedModules.IntegerQuotient.quotientGradedSMul _ _

theorem integerQuotientGrading_nat (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) :
    integerQuotientGrading I (d : ℤ) = Graded.Quotient.GradedHilbert.quotientGrading I d := by
  unfold integerQuotientGrading IntegerGradedQuotient.GradedModules.IntegerQuotient.grading
  rw [IntegerPolynomialGrading.GradedModules.polynomialIntegerGrading_nat]
  rfl

def integerDegreeQuotientEquiv (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d ≃ₗ[R] integerQuotientGrading I (d : ℤ) :=
  (Graded.Quotient.GradedHilbert.degreeQuotientEquivQuotientGrading I d).trans
    (LinearEquiv.ofEq _ _ (integerQuotientGrading_nat I d).symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert
