import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.ChangeCechExactness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RegularCoordinateFlag

/-! # Infinite Field Cech Bound -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.InfiniteFieldCechBound.GradedHilbert

noncomputable section

/-! Uniform graded Čech vanishing for saturated homogeneous ideals over every infinite field. The bound depends only on the ambient dimension and Hilbert polynomial. -/

open _root_.MvPolynomial

universe u

theorem saturated_cech_exact_infinite_field {K : Type u} [Field K] [Infinite K] {n : ℕ}
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P) :
    ∀ d : ℤ, (RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P : ℤ) ≤ d → ∀ q : ℕ,
      Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal)
        (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q := by
  induction n generalizing P with
  | zero =>
    intro d hd q
    exact Projective.ZeroCech.GradedHilbert.projectiveZero_moduleCechExactAt I hSat d hd q
  | succ n ih =>
    obtain ⟨l, hl, hl0, hreg⟩ := RegularLinearForm.GradedHilbert.exists_regular_linear_form I hSat
    obtain ⟨e, he⟩ := Linear.Changes.GradedHilbert.exists_coordinate_change l hl hl0
    let J := InfiniteFieldBound.GradedHilbert.changedIdeal e I
    have hJreg : RegularInitialIdeal.GradedHilbert.VariableRegular J.toIdeal 0 := by
      intro f hf
      apply hreg
      change Linear.Changes.GradedHilbert.extendLinearEquiv e (X 0 * f) ∈ I.toIdeal at hf
      rw [map_mul, he] at hf
      exact hf
    have hJP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial J.toIdeal P :=
      (InfiniteFieldBound.GradedHilbert.hasHilbertPolynomial_changedIdeal_iff e I P).mpr hP
    have hhyper := ih (Projective.Saturation.GradedHilbert.projectiveSaturation (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal J))
      (Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated _) (HyperplanePolynomial.GradedHilbert.hilbertDifference P)
      (HyperplanePolynomial.GradedHilbert.saturated_coordinateHyperplane_hasHilbertPolynomial J hJreg P hJP)
    have hJexact := HyperplaneRegularityDescent.GradedHilbert.coordinate_cech_exact_of_saturated_regular_hyperplane J hJreg.isSaturated
      hJreg P hJP (RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n (HyperplanePolynomial.GradedHilbert.hilbertDifference P)) hhyper
    intro d hd q
    exact (Linear.ChangeCechExactness.GradedHilbert.changedIdeal_moduleCechExactAt_iff e I d q).mp (hJexact d hd q)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.InfiniteFieldCechBound.GradedHilbert
