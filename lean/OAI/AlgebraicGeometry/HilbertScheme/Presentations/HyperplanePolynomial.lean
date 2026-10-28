import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.FormFunction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplaneDegreeEquivalence
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Truncation

/-! # Hyperplane Polynomial -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplanePolynomial.GradedHilbert

noncomputable section

/-! Regular hyperplane sections have the finite-difference Hilbert polynomial. -/

open _root_.MvPolynomial

universe u

def hilbertDifference (P : Polynomial ℚ) : Polynomial ℚ :=
  P - P.comp (Polynomial.X - 1)

theorem hilbertDifference_eval (P : Polynomial ℚ) (d : ℚ) :
    (hilbertDifference P).eval d = P.eval d - P.eval (d - 1) := by
  simp only [hilbertDifference, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_X,
    Polynomial.eval_one]

variable {K : Type u} [Field K] {n : ℕ}

theorem linearForm_hasHilbertPolynomial (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n))
    (l : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hl : l.IsHomogeneous 1)
    (hreg : ∀ f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n, l * f ∈ I.toIdeal → f ∈ I.toIdeal)
    (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Linear.FormQuotient.GradedHilbert.linearFormQuotientIdeal I l hl).toIdeal (hilbertDifference P) := by
  obtain ⟨N, hN⟩ := hP
  refine ⟨N + 1, fun d hd => ?_⟩
  have hd0 : 1 ≤ d := by omega
  have h := Linear.FormFunction.GradedHilbert.linearForm_hilbertFunction I l hl hreg (d - 1)
  rw [Nat.sub_add_cancel hd0] at h
  have h' : (Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal (d - 1) : ℚ) +
      (Hilbert.Polynomial.GradedHilbert.hilbertFunction (Linear.FormQuotient.GradedHilbert.linearFormQuotientIdeal I l hl).toIdeal d : ℚ) =
      (Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d : ℚ) := by exact_mod_cast h
  rw [hN (d - 1) (by omega), hN d (by omega), Nat.cast_sub hd0, Nat.cast_one] at h'
  rw [hilbertDifference_eval]
  linarith

theorem coordinateHyperplane_hasHilbertPolynomial
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K (n + 1)))
    (hreg : ∀ f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K (n + 1), X 0 * f ∈ I.toIdeal → f ∈ I.toIdeal)
    (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I).toIdeal (hilbertDifference P) := by
  obtain ⟨N, hN⟩ := linearForm_hasHilbertPolynomial I (X 0) (isHomogeneous_X K 0) hreg P hP
  exact ⟨N, fun d hd => (congrArg (fun a : ℕ => (a : ℚ)) (HyperplaneDegreeEquivalence.GradedHilbert.coordinateHyperplane_hilbertFunction I d)).symm.trans
    (hN d hd)⟩

theorem saturated_coordinateHyperplane_hasHilbertPolynomial
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K (n + 1)))
    (hreg : ∀ f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K (n + 1), X 0 * f ∈ I.toIdeal → f ∈ I.toIdeal)
    (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Projective.Saturation.GradedHilbert.projectiveSaturation (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I)).toIdeal (hilbertDifference P) :=
  (Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff _ _).mpr (coordinateHyperplane_hasHilbertPolynomial I hreg P hP)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplanePolynomial.GradedHilbert
