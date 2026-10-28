import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ChartSectionMap
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.Intersections
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RegularSections

/-! # Coordinate Evaluation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.CoordinateEvaluation.Dolbeault

noncomputable section

/-! Original regular evaluation of the coordinate-hyperplane local equation
is the ordinary projective coordinate ratio in the native analytic atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveNativeChartPoint (n : ℕ) (i : Fin (n + 1))
    (z : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) :=
  Open.AffineIsoEvaluation.affineIsoPointInOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
    (CommAlgCat.of ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)) (Foundations.Scheme.ProjectiveChart.projectiveCoordinateOverIso n i)
    ((ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph {j : Fin (n + 1) // j ≠ i}).symm z)

theorem projectiveNativeChartPoint_val (n : ℕ) (i : Fin (n + 1))
    (z : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    (projectiveNativeChartPoint n i z).val = ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint n i z := by
  have he : (Foundations.Scheme.ProjectiveChart.projectiveCoordinateOverIso n i).inv ≫
      Open.AffineIsoEvaluation.openInclusion (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) =
        ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineChartOverMap n i := by
    apply Over.OverMorphism.ext
    rfl
  exact (Open.AffineIsoEvaluation.affineIsoPointInOpen_val (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
    (CommAlgCat.of ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)) (Foundations.Scheme.ProjectiveChart.projectiveCoordinateOverIso n i)
    ((ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph {j : Fin (n + 1) // j ≠ i}).symm z)).trans
      (congrArg (fun f => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap
        (CommAlgCat.of ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)) f
        ((ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph {j : Fin (n + 1) // j ≠ i}).symm z)) he)

theorem sectionEvaluationOn_projectiveChart (n : ℕ) (i : Fin (n + 1))
    (z : {j : Fin (n + 1) // j ≠ i} → ℂ)
    (s : Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) :
    Open.AffineIsoEvaluation.sectionEvaluationOn (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) s
        (projectiveNativeChartPoint n i z) =
      MvPolynomial.eval z (ChartSectionMap.projectiveCoordinateSectionMap n i s) :=
  Open.AffineIsoEvaluation.sectionEvaluationOn_affineIso (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
    (CommAlgCat.of ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)) (Foundations.Scheme.ProjectiveChart.projectiveCoordinateOverIso n i)
    ((ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph {j : Fin (n + 1) // j ≠ i}).symm z) s

theorem projectiveLocalEquation_evaluation (n : ℕ) (i : Fin (n + 1))
    (j : {j : Fin (n + 1) // j ≠ i})
    (p : Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) :
    Holomorphic.RegularSections.regularHolomorphicSectionMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
        (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := ℂ) i j.val) p =
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j.val ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val) := by
  have hp : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val) := by
    apply (Intersections.Dolbeault.mem_projectiveStandardCover n i p.val).mp
    rw [Intersections.Dolbeault.projectiveStandardCover_eq_analyticOpen]
    exact p.property
  let z : {k : Fin (n + 1) // k ≠ i} → ℂ :=
    fun k => Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i k.val ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val)
  have he : projectiveNativeChartPoint n i z = p := by
    apply Subtype.ext
    exact (projectiveNativeChartPoint_val n i z).trans
      (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.projectivePoint_eq_affinePoint_on_patch n i p.val hp).symm
  change Open.AffineIsoEvaluation.sectionEvaluationOn (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := ℂ) i j.val) p = z j
  rw [← he, sectionEvaluationOn_projectiveChart, ChartSectionMap.projectiveCoordinateSectionMap_localEquation,
    MvPolynomial.eval_X]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.CoordinateEvaluation.Dolbeault
