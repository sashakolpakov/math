import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ContractedHomogeneousQuotient
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal

/-! # Contracted Ideal Localization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ContractedIdealLocalization.GradedHilbert

noncomputable section

/-! Contracting a homogeneous ideal from a coefficient localization and
extending it back recovers the original ideal exactly. -/

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] {n : ℕ}

theorem contractedHomogeneousIdeal_localization (M : Submonoid R) [IsLocalization M A]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading A n)) :
    Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I) = I := by
  let : Algebra (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Hilbert.Polynomial.GradedHilbert.CoordinateRing A n) := MvPolynomial.algebraMvPolynomial
  apply HomogeneousIdeal.ext
  change Ideal.map (algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Hilbert.Polynomial.GradedHilbert.CoordinateRing A n))
    (I.toIdeal.under (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) = I.toIdeal
  exact IsLocalization.map_under (M := M.map (MvPolynomial.C (σ := Fin (n + 1))))
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing A n) I.toIdeal

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ContractedIdealLocalization.GradedHilbert
