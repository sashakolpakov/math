import OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplaneRegularityDescent
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ZeroCech

/-! # Regular Coordinate Flag -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.RegularCoordinateFlag.GradedHilbert

noncomputable section

/-! A uniform degree bound for successive regular coordinate hyperplane sections.
The hypotheses concern multiplication by the actual coordinate variables in the
successive saturated quotients; they do not assume any Čech exactness. -/

open _root_.MvPolynomial

universe u

def HasRegularCoordinateFlag {K : Type u} [Field K] :
    {n : ℕ} → HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n) → Prop
  | 0, _ => True
  | n + 1, I => RegularInitialIdeal.GradedHilbert.VariableRegular I.toIdeal 0 ∧
      HasRegularCoordinateFlag (n := n) (Projective.Saturation.GradedHilbert.projectiveSaturation (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I))

def regularCoordinateFlagBound : ℕ → Polynomial ℚ → ℕ
  | 0, _ => 0
  | n + 1, P => max (regularCoordinateFlagBound n (HyperplanePolynomial.GradedHilbert.hilbertDifference P))
      (HyperplaneSaturationBound.GradedHilbert.hyperplaneSaturationBound.{u} n P)

theorem regularCoordinateFlag_cech_exact {K : Type u} [Field K] {n : ℕ}
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    (hflag : GradedHilbert.HasRegularCoordinateFlag I) (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P) :
    ∀ d : ℤ, (GradedHilbert.regularCoordinateFlagBound.{u} n P : ℤ) ≤ d → ∀ q : ℕ,
      Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal)
        (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q := by
  induction n generalizing P with
  | zero =>
    intro d hd q
    exact Projective.ZeroCech.GradedHilbert.projectiveZero_moduleCechExactAt I hSat d hd q
  | succ n ih =>
    obtain ⟨hreg, hflag'⟩ := hflag
    apply HyperplaneRegularityDescent.GradedHilbert.coordinate_cech_exact_of_saturated_regular_hyperplane I hSat hreg P hP
      (GradedHilbert.regularCoordinateFlagBound.{u} n (HyperplanePolynomial.GradedHilbert.hilbertDifference P))
    exact ih (Projective.Saturation.GradedHilbert.projectiveSaturation (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I)) (Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated _)
      hflag' (HyperplanePolynomial.GradedHilbert.hilbertDifference P) (HyperplanePolynomial.GradedHilbert.saturated_coordinateHyperplane_hasHilbertPolynomial I hreg P hP)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.RegularCoordinateFlag.GradedHilbert
