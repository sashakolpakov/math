import OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplaneScalarAlgebra
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmbeddedCechExactness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.ModuleIsomorphism
import Mathlib.Order.Fin.Basic

/-! # Hyperplane Cech Exactness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplaneCechExactness.GradedHilbert

noncomputable section

/-! The actual coordinate-hyperplane quotient has the Čech exactness of its smaller projective coordinate ring. -/

open _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

attribute [local instance] HyperplaneScalarAlgebra.GradedHilbert.coordinateDeletionAlgebra

theorem coordinateHyperplane_moduleCechExactAt_iff
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R (n + 1))) (d : ℤ) (q : ℕ) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1 + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R (n + 1) ⧸ (Linear.FormQuotient.GradedHilbert.linearFormQuotientIdeal I (X 0) (isHomogeneous_X R 0)).toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Linear.FormQuotient.GradedHilbert.linearFormQuotientIdeal I (X 0) (isHomogeneous_X R 0))) d q ↔
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I).toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I)) d q := by
  have h₁ := Cech.ModuleIsomorphism.ProjectiveCech.moduleCechExactAt_iff_of_module_bijective R
    (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Linear.FormQuotient.GradedHilbert.linearFormQuotientIdeal I (X 0) (isHomogeneous_X R 0)))
    (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I))
    (HyperplaneScalarAlgebra.GradedHilbert.coordinateHyperplanePolynomialEquiv I).toLinearMap
    (HyperplaneScalarAlgebra.GradedHilbert.coordinateHyperplanePolynomialEquiv_homogeneous I) (HyperplaneScalarAlgebra.GradedHilbert.coordinateHyperplanePolynomialEquiv I).bijective d q
  have h₂ := EmbeddedCechExactness.ProjectiveCech.embedded_moduleCechExactAt_iff R (Fin.succOrderEmb (n + 1)) rfl
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I).toIdeal)
    (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I)) d q
  exact h₁.trans h₂

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplaneCechExactness.GradedHilbert
