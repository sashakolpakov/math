import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapRatioUnits
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions

/-! # Projective Ratio -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ProjectiveRatio

noncomputable section

/-! The Presentations overlap coordinate unit is exactly the native transition
unit used in the projective twist constructions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ} (i j : Fin (n + 1))

theorem nativeProjectiveLocalEquation_eq :
    SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := K) i j =
      (Proj.basicOpenIsoAway (Hilbert.Polynomial.GradedHilbert.grading K n) (X i) (isHomogeneous_X K i) Nat.zero_lt_one).hom
        (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j)) := by
  rw [SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_eq_isLocalizationElem]
  apply congrArg
    (Proj.basicOpenIsoAway (Hilbert.Polynomial.GradedHilbert.grading K n) (X i) (isHomogeneous_X K i) Nat.zero_lt_one).hom
  simp only [Polynomial.Dehomogenization.PolynomialProjective.dehomogenize_X, Polynomial.Dehomogenization.PolynomialProjective.coordinateFraction, HomogeneousLocalization.Away.isLocalizationElem, pow_one]

theorem projectiveOverlapRatio_eq_native :
    Projective.OverlapSectionUnits.projectiveOverlapRatio K i j =
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := K) i j :
        Γ(Proj (homogeneousSubmodule (Fin (n + 1)) K), SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := K) i j)) := by
  change Projective.OverlapSectionUnits.projectiveOverlapRatio K i j = (Proj (Hilbert.Polynomial.GradedHilbert.grading K n)).presheaf.map
    (homOfLE (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := K) i j)).op (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := K) i j)
  rw [nativeProjectiveLocalEquation_eq]
  have h := Proj.awayMap_awayToSection (Hilbert.Polynomial.GradedHilbert.grading K n) (isHomogeneous_X K j)
    (rfl : X i * X j = X i * X j)
  exact congrArg (fun f => f (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize (R := K) i (X j))) h

theorem projectiveOverlapRatioUnit_eq_native :
    Projective.OverlapRatioUnits.projectiveOverlapRatioUnit K i j = SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := K) i j := by
  apply Units.ext
  rw [Projective.OverlapRatioUnits.projectiveOverlapRatioUnit_value, projectiveOverlapRatio_eq_native]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ProjectiveRatio
