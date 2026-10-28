import OAI.AlgebraicGeometry.Comparison.Betti.Projective.CoordinateEvaluation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.SpaceChart

/-! # Chart Evaluation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.ChartEvaluation.Dolbeault

noncomputable section

/-! Evaluation of every original projective chart section in the algebraic Laurent chart coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveChartSection_evaluation (n : ℕ) (i : Fin (n + 1))
    (p : Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i))
    (s : Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) :
    Holomorphic.RegularSections.regularHolomorphicSectionMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) s p =
      MvPolynomial.eval (fun j : {j : Fin (n + 1) // j ≠ i} =>
        Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j.val ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val))
        (ChartSectionMap.projectiveCoordinateSectionMap n i s) := by
  have hp : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val) := by
    apply (Intersections.Dolbeault.mem_projectiveStandardCover n i p.val).mp
    rw [Intersections.Dolbeault.projectiveStandardCover_eq_analyticOpen]
    exact p.property
  let z : {j : Fin (n + 1) // j ≠ i} → ℂ :=
    fun j => Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j.val ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val)
  have he : CoordinateEvaluation.Dolbeault.projectiveNativeChartPoint n i z = p := by
    apply Subtype.ext
    exact (CoordinateEvaluation.Dolbeault.projectiveNativeChartPoint_val n i z).trans
      (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.projectivePoint_eq_affinePoint_on_patch n i p.val hp).symm
  change Open.AffineIsoEvaluation.sectionEvaluationOn (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) s p = _
  exact (congrArg (fun p => Open.AffineIsoEvaluation.sectionEvaluationOn (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) s p) he).symm.trans (CoordinateEvaluation.Dolbeault.sectionEvaluationOn_projectiveChart n i z s)

theorem projectiveChartToPolynomial_eq_laurentChart (n : ℕ) (i : Fin (n + 1))
    (p : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n i) :
    Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i p = SheafCohomology.Projective.SpaceChart.MvPolynomial.chartRingEquiv ℂ i p := by
  classical
  have he : Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize (R := ℂ) i =
      SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAux ℂ i := by
    apply MvPolynomial.ringHom_ext
    · intro c
      exact (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize_C i c).trans
        (SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAux_C ℂ i c).symm
    · intro j
      by_cases hj : j = i
      · subst j
        exact (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize_X_self i).trans
          (SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAux_X_self ℂ i).symm
      · exact (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize_X_of_ne i j hj).trans
          (SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAux_X_ne ℂ i hj).symm
  obtain ⟨k, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _
    (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) p
  rw [Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial_mk]
  change Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i f =
    SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAt ℂ i
      (HomogeneousLocalization.Away.mk _ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) k f hf)
  rw [SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAt_mk]
  exact DFunLike.congr_fun he f

theorem projectiveChartToPolynomial_eq_laurentChart_with_decidable (n : ℕ) (i : Fin (n + 1))
    (δ : DecidableEq (Fin (n + 1))) (p : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n i) :
    Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i p = @SheafCohomology.Projective.SpaceChart.MvPolynomial.chartRingEquiv ℂ (Fin (n + 1)) _ δ i p := by
  have hδ : instDecidableEqFin (n + 1) = δ := Subsingleton.elim _ _
  exact (projectiveChartToPolynomial_eq_laurentChart n i p).trans
    (congrArg (fun δ => @SheafCohomology.Projective.SpaceChart.MvPolynomial.chartRingEquiv ℂ (Fin (n + 1)) _ δ i p) hδ)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.ChartEvaluation.Dolbeault
