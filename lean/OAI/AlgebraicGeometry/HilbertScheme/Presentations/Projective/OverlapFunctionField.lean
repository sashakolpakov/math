import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.FunctionFieldRestrictions
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapSectionUnits

/-! # Overlap Function Field -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapFunctionField

noncomputable section

/-! Actual overlap sections map canonically to rational functions,
preserving their coordinate ratios and field constants. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ} (i j : Fin (n + 1))

def projectiveDoubleFunctionFieldMap : DoubleChartUnits.ProjectiveDoubleChartRing K i j →+*
    FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :=
  Homogeneous.ChartFunctionField.homogeneousChartFunctionFieldMap K (X i * X j) (mul_ne_zero (X_ne_zero i) (X_ne_zero j))

theorem projectiveDoubleFunctionFieldMap_chart :
    (projectiveDoubleFunctionFieldMap K i j).comp (DoubleChartUnits.projectiveDoubleChartMap K i j) =
      Homogeneous.ChartFunctionField.homogeneousChartFunctionFieldMap K (X i) (X_ne_zero i) :=
  Homogeneous.FunctionFieldRestrictions.homogeneousChartFunctionFieldMap_awayMap K (X i) (X j) (X_ne_zero i) (X_ne_zero j) (isHomogeneous_X K j)

theorem projectiveDoubleFunctionFieldMap_ratio :
    projectiveDoubleFunctionFieldMap K i j (DoubleChartUnits.projectiveDoubleChartRatio K i j) =
      RationalCoordinateDegrees.rationalProjectiveCoordinate (K := K) i j :=
  (RingHom.congr_fun (projectiveDoubleFunctionFieldMap_chart K i j) (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j))).trans
    (Homogeneous.ChartFunctionField.homogeneousChartFunctionFieldMap_coordinate K i j)

theorem projectiveDoubleFunctionFieldMap_constant (c : K) :
    projectiveDoubleFunctionFieldMap K i j (DoubleChartUnits.projectiveDoubleChartConstant K i j c) =
      algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (C c) := by
  have h := RingHom.congr_fun (projectiveDoubleFunctionFieldMap_chart K i j)
    (algebraMap K (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing K n i) c)
  change projectiveDoubleFunctionFieldMap K i j (DoubleChartUnits.projectiveDoubleChartConstant K i j c) =
    Homogeneous.ChartFunctionField.homogeneousChartFunctionFieldMap K (X i) (X_ne_zero i) (algebraMap K (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing K n i) c) at h
  rw [← AbelianModuli.HilbertConstruction.ProjectiveChart.Algebra.projectiveChart_dehomogenize_constant, Polynomial.Dehomogenization.PolynomialProjective.dehomogenize_C] at h
  exact h.trans (Homogeneous.ChartFunctionField.homogeneousChartFunctionFieldMap_constant K i c)

def projectiveOverlapFunctionFieldMap :
    Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j) →+*
      FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :=
  (projectiveDoubleFunctionFieldMap K i j).comp (OverlapSectionUnits.projectiveDoubleSectionIso K i j).inv.hom

theorem projectiveOverlapFunctionFieldMap_ratio :
    projectiveOverlapFunctionFieldMap K i j (OverlapSectionUnits.projectiveOverlapRatio K i j) =
      RationalCoordinateDegrees.rationalProjectiveCoordinate (K := K) i j := by
  change projectiveDoubleFunctionFieldMap K i j
      ((OverlapSectionUnits.projectiveDoubleSectionIso K i j).inv ((OverlapSectionUnits.projectiveDoubleSectionIso K i j).hom
        (DoubleChartUnits.projectiveDoubleChartRatio K i j))) = _
  rw [Iso.hom_inv_id_apply, projectiveDoubleFunctionFieldMap_ratio]

theorem projectiveOverlapFunctionFieldMap_constant (c : K) :
    projectiveOverlapFunctionFieldMap K i j (OverlapSectionUnits.projectiveOverlapConstant K i j c) =
      algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (C c) := by
  change projectiveDoubleFunctionFieldMap K i j
      ((OverlapSectionUnits.projectiveDoubleSectionIso K i j).inv ((OverlapSectionUnits.projectiveDoubleSectionIso K i j).hom
        (DoubleChartUnits.projectiveDoubleChartConstant K i j c))) = _
  rw [Iso.hom_inv_id_apply, projectiveDoubleFunctionFieldMap_constant]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapFunctionField
