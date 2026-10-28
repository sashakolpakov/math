import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ChartFractions
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LineParameter

/-! # Chart Fractions -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.ChartFractions

noncomputable section

/-! Pullback of a projective coordinate fraction to its polynomial
chart is the native stalk germ of the dehomogenized polynomial. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

theorem contained (n : ℕ) (i : Fin (n + 1)) (x : Spec (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))) :
    Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i :=
  ((Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).inv x).property

theorem fraction (n : ℕ) (i : Fin (n + 1)) (x : Spec (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)))
    (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :
    GermPullback.fraction n (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i) x a
      (Projective.LineParameter.RationalFractions.coordinate n i) (contained n i x) =
    StructureSheaf.toStalk (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i) x
      (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i a.val) := by
  have hchart : Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i =
      Spec.map (CommRingCat.ofHom (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i)) ≫
        AwayChartPullback.chart n (Projective.LineParameter.RationalFractions.coordinate n i) :=
    Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec_inv_ι n i
  have hc : a.val ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 := a.property
  have hs : (Projective.LineParameter.RationalFractions.coordinate n i).val ∉
      ((Spec.map (CommRingCat.ofHom (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i)) ≫
        AwayChartPullback.chart n (Projective.LineParameter.RationalFractions.coordinate n i)) x).asHomogeneousIdeal := by
    rw [← hchart]
    exact contained n i x
  rw [GermPullback.fraction_congr n _ _ hchart x a
      (Projective.LineParameter.RationalFractions.coordinate n i) (contained n i x) hs,
    GermPullback.fraction_comp, AwayChartPullback.fraction]
  exact (Projection.ChartFractions.spec_germ
    (CommRingCat.ofHom (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i)) x
      (Away.mk (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) 1 a.val hc)).trans
    (congrArg (StructureSheaf.toStalk (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i) x)
      (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial_mk n i 1 a.val hc))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.ChartFractions
