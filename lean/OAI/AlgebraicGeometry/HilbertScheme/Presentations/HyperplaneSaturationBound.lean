import OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplanePolynomial

/-! # Hyperplane Saturation Bound -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplaneSaturationBound.GradedHilbert

noncomputable section

/-! A bound depending only on the Hilbert polynomial for saturation of a regular coordinate hyperplane section. -/

open _root_.MvPolynomial

universe u

def hyperplaneSaturationBound (n : ℕ) (P : Polynomial ℚ) : ℕ :=
  max (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} (n + 1) P + 1) (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n (HyperplanePolynomial.GradedHilbert.hilbertDifference P))

theorem coordinateHyperplane_uniform_hilbertFunction {K : Type u} [Field K] {n : ℕ}
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K (n + 1))) (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    (hreg : ∀ f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K (n + 1), X 0 * f ∈ I.toIdeal → f ∈ I.toIdeal)
    (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P)
    (d : ℕ) (hd : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} (n + 1) P + 1 ≤ d) :
    (Hilbert.Polynomial.GradedHilbert.hilbertFunction (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I).toIdeal d : ℚ) = (HyperplanePolynomial.GradedHilbert.hilbertDifference P).eval (d : ℚ) := by
  have hd0 : 1 ≤ d := by omega
  have h := Linear.FormFunction.GradedHilbert.linearForm_hilbertFunction I (X 0) (isHomogeneous_X K 0) hreg (d - 1)
  rw [Nat.sub_add_cancel hd0, HyperplaneDegreeEquivalence.GradedHilbert.coordinateHyperplane_hilbertFunction] at h
  have h' : (Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal (d - 1) : ℚ) +
      (Hilbert.Polynomial.GradedHilbert.hilbertFunction (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I).toIdeal d : ℚ) =
      (Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d : ℚ) := by exact_mod_cast h
  have hp := (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec (n + 1) P K I hSat hP).2
  rw [hp (d - 1) (by omega), hp d (by omega), Nat.cast_sub hd0, Nat.cast_one] at h'
  rw [HyperplanePolynomial.GradedHilbert.hilbertDifference_eval]
  linarith

theorem coordinateHyperplane_uniform_saturation {K : Type u} [Field K] {n : ℕ}
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K (n + 1))) (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    (hreg : ∀ f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K (n + 1), X 0 * f ∈ I.toIdeal → f ∈ I.toIdeal)
    (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P)
    (d : ℕ) (hd : hyperplaneSaturationBound.{u} n P ≤ d) :
    Hilbert.Polynomial.GradedHilbert.degreeRelations (Projective.Saturation.GradedHilbert.projectiveSaturation (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I)).toIdeal d =
      Hilbert.Polynomial.GradedHilbert.degreeRelations (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I).toIdeal d := by
  have hraw := coordinateHyperplane_uniform_hilbertFunction I hSat hreg P hP d ((le_max_left _ _).trans hd)
  have hsat := (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec n (HyperplanePolynomial.GradedHilbert.hilbertDifference P) K
    (Projective.Saturation.GradedHilbert.projectiveSaturation (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I)) (Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated _)
    (HyperplanePolynomial.GradedHilbert.saturated_coordinateHyperplane_hasHilbertPolynomial I hreg P hP)).2 d ((le_max_right _ _).trans hd)
  have he : Hilbert.Polynomial.GradedHilbert.hilbertFunction (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I).toIdeal d =
      Hilbert.Polynomial.GradedHilbert.hilbertFunction (Projective.Saturation.GradedHilbert.projectiveSaturation (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I)).toIdeal d := by
    exact_mod_cast hraw.trans hsat.symm
  exact (Hilbert.Polynomial.GradedHilbert.degreeRelations_eq_of_le_of_hilbertFunction_eq (Projective.Saturation.GradedHilbert.le_projectiveSaturation _) d he).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplaneSaturationBound.GradedHilbert
