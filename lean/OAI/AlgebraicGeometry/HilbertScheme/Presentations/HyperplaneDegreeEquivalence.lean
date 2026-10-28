import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.Hyperplane
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Exactness

/-! # Hyperplane Degree Equivalence -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplaneDegreeEquivalence.GradedHilbert

noncomputable section

/-! Coordinate-hyperplane quotient isomorphisms identify the actual homogeneous degree quotients. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Exactness.GradedModules

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R (n + 1)))

theorem coordinateHyperplaneQuotientEquiv_homogeneous (d : ℕ)
    (x : Hilbert.Polynomial.GradedHilbert.CoordinateRing R (n + 1) ⧸ (Linear.FormQuotient.GradedHilbert.linearFormQuotientIdeal I (X 0) (isHomogeneous_X R 0)).toIdeal)
    (hx : x ∈ Graded.Quotient.GradedHilbert.quotientGrading (Linear.FormQuotient.GradedHilbert.linearFormQuotientIdeal I (X 0) (isHomogeneous_X R 0)) d) :
    Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneQuotientEquiv I x ∈ Graded.Quotient.GradedHilbert.quotientGrading (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I) d := by
  obtain ⟨f, hf, rfl⟩ := hx
  change Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneQuotientEquiv I (Ideal.Quotient.mk _ f) ∈ _
  rw [Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneQuotientEquiv_mk]
  exact ⟨Coordinate.Hyperplane.GradedHilbert.forgetZeroCoordinate R n f, Coordinate.Hyperplane.GradedHilbert.forgetZeroCoordinate_homogeneous R n hf, rfl⟩

def coordinateHyperplaneGradingEquiv (d : ℕ) :
    Graded.Quotient.GradedHilbert.quotientGrading (Linear.FormQuotient.GradedHilbert.linearFormQuotientIdeal I (X 0) (isHomogeneous_X R 0)) d ≃ₗ[R]
      Graded.Quotient.GradedHilbert.quotientGrading (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I) d :=
  LinearEquiv.ofBijective (Graded.Exactness.GradedModules.degreeMap _ _ (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneQuotientEquiv I).toLinearMap
    (coordinateHyperplaneQuotientEquiv_homogeneous I) d) ⟨by
      intro x y hxy
      exact Subtype.ext ((Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneQuotientEquiv I).injective (congrArg Subtype.val hxy)),
    Graded.Exactness.GradedModules.degreeMap_surjective _ _ (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneQuotientEquiv I).toLinearMap
      (coordinateHyperplaneQuotientEquiv_homogeneous I) (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneQuotientEquiv I).surjective d⟩

def coordinateHyperplaneDegreeQuotientEquiv (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Linear.FormQuotient.GradedHilbert.linearFormQuotientIdeal I (X 0) (isHomogeneous_X R 0)).toIdeal d ≃ₗ[R]
      Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I).toIdeal d :=
  (Graded.Quotient.GradedHilbert.degreeQuotientEquivQuotientGrading _ d).trans ((coordinateHyperplaneGradingEquiv I d).trans
    (Graded.Quotient.GradedHilbert.degreeQuotientEquivQuotientGrading _ d).symm)

theorem coordinateHyperplane_hilbertFunction (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.hilbertFunction (Linear.FormQuotient.GradedHilbert.linearFormQuotientIdeal I (X 0) (isHomogeneous_X R 0)).toIdeal d =
      Hilbert.Polynomial.GradedHilbert.hilbertFunction (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I).toIdeal d :=
  (coordinateHyperplaneDegreeQuotientEquiv I d).finrank_eq

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplaneDegreeEquivalence.GradedHilbert
