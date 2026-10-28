import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalCoordinateDegrees
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Dehomogenization

/-! # Chart Function Field -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ChartFunctionField

noncomputable section

/-! Canonical maps from homogeneous projective chart rings to the
polynomial function field send coordinate fractions to their actual ratios. -/

open _root_.MvPolynomial _root_.HomogeneousLocalization

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective

universe u
variable (K : Type u) [Field K] {n : ℕ}

def localizationFunctionFieldMap (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hf : f ≠ 0) :
    Localization.Away f →+* FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :=
  IsLocalization.Away.lift f (isUnit_iff_ne_zero.mpr (RationalCoordinateDegrees.polynomialFunctionField_ne_zero hf))

theorem localizationFunctionFieldMap_algebraMap (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hf : f ≠ 0)
    (r : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :
    localizationFunctionFieldMap K f hf (algebraMap _ (Localization.Away f) r) =
      algebraMap _ (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) r :=
  IsLocalization.Away.lift_eq _ _ _

theorem localizationFunctionFieldMap_invSelf (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hf : f ≠ 0) :
    localizationFunctionFieldMap K f hf (IsLocalization.Away.invSelf f) =
      (algebraMap _ (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) f)⁻¹ := by
  apply mul_left_cancel₀ (RationalCoordinateDegrees.polynomialFunctionField_ne_zero hf)
  rw [mul_inv_cancel₀ (RationalCoordinateDegrees.polynomialFunctionField_ne_zero hf)]
  calc
    _ = localizationFunctionFieldMap K f hf
        (algebraMap _ (Localization.Away f) f * IsLocalization.Away.invSelf f) := by
      rw [map_mul, localizationFunctionFieldMap_algebraMap]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]

def homogeneousChartFunctionFieldMap (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hf : f ≠ 0) :
    HomogeneousLocalization.Away (Hilbert.Polynomial.GradedHilbert.grading K n) f →+*
      FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :=
  (localizationFunctionFieldMap K f hf).comp (algebraMap _ (Localization.Away f))

theorem homogeneousChartFunctionFieldMap_coordinate (i j : Fin (n + 1)) :
    homogeneousChartFunctionFieldMap K (X i) (X_ne_zero i) (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j)) =
      RationalCoordinateDegrees.rationalProjectiveCoordinate (K := K) i j := by
  change localizationFunctionFieldMap K (X i) (X_ne_zero i) (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j)).val = _
  rw [Polynomial.Dehomogenization.PolynomialProjective.dehomogenize_X, Polynomial.Dehomogenization.PolynomialProjective.val_coordinateFraction, pow_one, map_mul,
    localizationFunctionFieldMap_algebraMap, localizationFunctionFieldMap_invSelf]
  rfl

theorem homogeneousChartFunctionFieldMap_constant (i : Fin (n + 1)) (c : K) :
    homogeneousChartFunctionFieldMap K (X i) (X_ne_zero i) (Polynomial.Dehomogenization.PolynomialProjective.chartConstants i c) =
      algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (C c) := by
  change localizationFunctionFieldMap K (X i) (X_ne_zero i) (Polynomial.Dehomogenization.PolynomialProjective.chartConstants i c).val = _
  rw [Polynomial.Dehomogenization.PolynomialProjective.val_chartConstants, localizationFunctionFieldMap_algebraMap]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ChartFunctionField
