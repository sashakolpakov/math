import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.HomogeneousRatios

/-! # Ratio Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.RatioCocycle

noncomputable section

/-! The actual homogeneous coordinate ratios satisfy the frame cocycle and are units when both coordinates are inverted. -/

open _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateHomogeneousRatio_self (s : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ s) :
    HomogeneousRatios.coordinateHomogeneousRatio I s i i hi = 1 := by
  apply HomogeneousLocalization.val_injective
  apply (HomogeneousRatios.coordinateChartVariable_isUnit I s i hi).mul_left_cancel
  rw [HomogeneousRatios.coordinateHomogeneousRatio_mul]
  simp only [HomogeneousLocalization.val_one, mul_one]

theorem coordinateHomogeneousRatio_comp (s : Finset (Fin (n + 1))) (i j k : Fin (n + 1))
    (hi : i ∈ s) (hj : j ∈ s) :
    HomogeneousRatios.coordinateHomogeneousRatio I s i j hi * HomogeneousRatios.coordinateHomogeneousRatio I s j k hj =
      HomogeneousRatios.coordinateHomogeneousRatio I s i k hi := by
  apply HomogeneousLocalization.val_injective
  apply (HomogeneousRatios.coordinateChartVariable_isUnit I s i hi).mul_left_cancel
  rw [HomogeneousLocalization.val_mul, ← mul_assoc, HomogeneousRatios.coordinateHomogeneousRatio_mul,
    HomogeneousRatios.coordinateHomogeneousRatio_mul, HomogeneousRatios.coordinateHomogeneousRatio_mul]

def coordinateHomogeneousRatioUnit (s : Finset (Fin (n + 1))) (i j : Fin (n + 1))
    (hi : i ∈ s) (hj : j ∈ s) :
    (HomogeneousLocalization.Away (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)))ˣ where
  val := HomogeneousRatios.coordinateHomogeneousRatio I s i j hi
  inv := HomogeneousRatios.coordinateHomogeneousRatio I s j i hj
  val_inv := (coordinateHomogeneousRatio_comp I s i j i hi hj).trans
    (coordinateHomogeneousRatio_self I s i hi)
  inv_val := (coordinateHomogeneousRatio_comp I s j i j hj hi).trans
    (coordinateHomogeneousRatio_self I s j hj)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.RatioCocycle
