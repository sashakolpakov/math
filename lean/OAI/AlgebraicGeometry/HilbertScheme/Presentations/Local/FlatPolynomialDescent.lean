import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FlatPolynomialConstancy
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.IdealTower
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SaturationBaseChangeEquality

/-! # Flat Polynomial Descent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FlatPolynomialDescent.GradedHilbert

noncomputable section

/-! A polynomial seen in one fiber of the original family descends to
its Noetherian local flat model, using exact saturated coordinate recovery. -/

open _root_.AlgebraicGeometry

universe u
variable {R A K : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable [CommRing A] [Field K] [Algebra R A] [Algebra A K] [Algebra R K]
variable [IsScalarTower R A K] {n : ℕ}

theorem localFlat_hilbertPolynomial_of_saturated_baseChange
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]
    (L : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading A n))
    (hL : L = Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I))
    (P : Polynomial ℚ)
    (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) L)).toIdeal P) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P := by
  have hs : Projective.Saturation.GradedHilbert.projectiveSaturation L = Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) := by
    rw [hL, Projective.Saturation.GradedHilbert.projectiveSaturation_idempotent]
  have he := Projective.SaturationBaseChangeEquality.GradedHilbert.projectiveSaturation_extended_eq_of_eq (A := K) L (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) hs
  rw [Homogeneous.IdealTower.GradedHilbert.extendedHomogeneousIdeal_tower] at he
  apply (FlatPolynomialConstancy.GradedHilbert.localFlat_saturated_fiber_polynomial_iff I K P).mp
  exact he ▸ hP

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FlatPolynomialDescent.GradedHilbert
