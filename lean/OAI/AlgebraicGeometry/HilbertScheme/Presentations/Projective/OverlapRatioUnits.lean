import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.FunctionFieldInjectivity

/-! # Overlap Ratio Units -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapRatioUnits

noncomputable section

/-! The standard coordinate ratio is an actual unit on each double
overlap. Its integer powers have the expected fraction-field values. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ} (i j : Fin (n + 1))

theorem projectiveDoubleChartRatio_isUnit : IsUnit (DoubleChartUnits.projectiveDoubleChartRatio K i j) :=
  IsLocalization.map_units (DoubleChartUnits.ProjectiveDoubleChartRing K i j)
    (⟨Polynomial.Dehomogenization.PolynomialProjective.dehomogenize (R := K) i (X j), Submonoid.mem_powers _⟩ :
      Submonoid.powers (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize (R := K) i (X j)))

theorem projectiveOverlapRatio_isUnit : IsUnit (OverlapSectionUnits.projectiveOverlapRatio K i j) :=
  (projectiveDoubleChartRatio_isUnit K i j).map (OverlapSectionUnits.projectiveDoubleSectionIso K i j).hom.hom

def projectiveOverlapRatioUnit : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j)ˣ :=
  (projectiveOverlapRatio_isUnit K i j).unit

theorem projectiveOverlapRatioUnit_value :
    (projectiveOverlapRatioUnit K i j : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j)) =
      OverlapSectionUnits.projectiveOverlapRatio K i j := (projectiveOverlapRatio_isUnit K i j).unit_spec

theorem projectiveOverlapRatioUnit_field_zpow (d : ℤ) :
    OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j
      ((projectiveOverlapRatioUnit K i j ^ d : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j)ˣ) :
        Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j)) =
      RationalCoordinateDegrees.rationalProjectiveCoordinate i j ^ d := by
  change ((Units.map (OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j).toMonoidHom
    (projectiveOverlapRatioUnit K i j ^ d)) : FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  change OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j (projectiveOverlapRatioUnit K i j : _) ^ d = _
  rw [projectiveOverlapRatioUnit_value, OverlapFunctionField.projectiveOverlapFunctionFieldMap_ratio]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapRatioUnits
