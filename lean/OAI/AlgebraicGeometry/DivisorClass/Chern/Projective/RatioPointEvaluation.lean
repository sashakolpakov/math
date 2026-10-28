import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ChartSectionMap
import OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticCover
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveScheme

/-! # Ratio Point Evaluation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RatioPointEvaluation

noncomputable section

section

/-! Evaluation of the constructed projective regular ratio is ordinary character evaluation in the actual affine chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def projectiveOpenChartCharacter (n : ℕ) (i : Fin (n + 1))
    (p : Line.Bundles.AlgebraicLineBundle.analyticOpen (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).presentation (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)).symm
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Foundations.Scheme.ProjectiveChart.projectiveCoordinateOverIso n i).hom
      ((Line.Bundles.AlgebraicLineBundle.openPointHomeomorph (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).presentation
        (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)).symm p))

theorem projectiveRegularRatio_character_evaluation (n : ℕ) (i j : Fin (n + 1))
    (p : Line.Bundles.AlgebraicLineBundle.analyticOpen (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).presentation (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) :
    Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).presentation (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
      (RegularRatios.projectiveRegularRatio n i j (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) le_rfl) p =
      projectiveOpenChartCharacter n i p
        (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i (RatioAwaySection.projectiveRatioAwayElement n i j)) := by
  let q := (Line.Bundles.AlgebraicLineBundle.openPointHomeomorph (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).presentation
    (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)).symm p
  let r := Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i (RatioAwaySection.projectiveRatioAwayElement n i j)
  let a := projectiveOpenChartCharacter n i p
  have ha : ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i) a =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Foundations.Scheme.ProjectiveChart.projectiveCoordinateOverIso n i).hom q :=
    (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)).apply_symm_apply _
  have hval := AnalyticTransitions.Construction.globalSectionEvaluation_affine (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i) a
    ((Scheme.ΓSpecIso (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))).inv r)
  rw [ha] at hval
  have hc := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))).inv_hom_id r
  change (Scheme.ΓSpecIso (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))).hom
    ((Scheme.ΓSpecIso (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))).inv r) = r at hc
  rw [hc] at hval
  change AnalyticTransitions.Construction.globalSectionEvaluation q ((Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).topIso.inv
    (RegularRatios.projectiveRegularRatio n i j (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) le_rfl)) = a r
  exact (congrArg (AnalyticTransitions.Construction.globalSectionEvaluation q) (ChartSectionMap.projectiveCoordinateIsoSpec_ratio_section n i j).symm).trans
    ((AnalyticTransitions.Construction.globalSectionEvaluation_map (Foundations.Scheme.ProjectiveChart.projectiveCoordinateOverIso n i).hom q
      ((Scheme.ΓSpecIso (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))).inv r)).symm.trans hval)

end

section

/-! The actual affine character of a projective open recovers its original complex point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem projectiveCoordinateChartOver_inclusion (n : ℕ) (i : Fin (n + 1)) :
    (Foundations.Scheme.ProjectiveChart.projectiveCoordinateOverIso n i).hom ≫ ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineChartOverMap n i =
      Line.Bundles.AlgebraicLineBundle.openInclusion (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).presentation (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) := by
  apply Over.OverMorphism.ext
  change (Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).hom ≫
    ((Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).inv ≫ (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι) =
    (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι
  rw [Iso.hom_inv_id_assoc]

theorem projectiveOpenChartCharacter_point (n : ℕ) (i : Fin (n + 1))
    (p : Line.Bundles.AlgebraicLineBundle.analyticOpen (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).presentation (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) :
    ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint n i
      (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph {j : Fin (n + 1) // j ≠ i} (projectiveOpenChartCharacter n i p)) = p.val := by
  let q := (Line.Bundles.AlgebraicLineBundle.openPointHomeomorph (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).presentation
    (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)).symm p
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineChartOverMap n i)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)
      ((ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph {j : Fin (n + 1) // j ≠ i}).symm
        (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph {j : Fin (n + 1) // j ≠ i} (projectiveOpenChartCharacter n i p)))) = _
  rw [Homeomorph.symm_apply_apply]
  have ha : ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i) (projectiveOpenChartCharacter n i p) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Foundations.Scheme.ProjectiveChart.projectiveCoordinateOverIso n i).hom q :=
    (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)).apply_symm_apply _
  rw [ha, ← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, projectiveCoordinateChartOver_inclusion]
  exact congrArg Subtype.val
    ((Line.Bundles.AlgebraicLineBundle.openPointHomeomorph (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).presentation
      (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)).apply_symm_apply p)

end

/-! Evaluation of the actual projective regular ratio equals the original homogeneous-coordinate ratio. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

theorem projectiveOpenChartCharacter_ratio (n : ℕ) (i j : Fin (n + 1))
    (p : Line.Bundles.AlgebraicLineBundle.analyticOpen (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).presentation (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) :
    projectiveOpenChartCharacter n i p
        (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i (RatioAwaySection.projectiveRatioAwayElement n i j)) =
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val) := by
  let z := ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph {j : Fin (n + 1) // j ≠ i} (projectiveOpenChartCharacter n i p)
  have hp : (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val =
      ((ComplexPoints.Analytic.ProjectiveCharts.projectiveAffineChart i).symm z).val := by
    apply (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).injective
    rw [Homeomorph.apply_symm_apply, ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph_apply]
    exact (projectiveOpenChartCharacter_point n i p).symm.trans
      (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint_eq_projectivization n i z)
  rw [hp]
  by_cases hji : j = i
  · subst j
    have hpatch : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i i ((ComplexPoints.Analytic.ProjectiveCharts.projectiveAffineChart i).symm z).val = 1 :=
      ((ComplexPoints.Analytic.ProjectiveCharts.projectiveAffineChart i).symm z).property
    rw [hpatch]
    simp only [RatioAwaySection.projectiveRatioAwayElement, Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial_mk,
      Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize_X_self, map_one]
  · have hr := congrArg (fun w : {j : Fin (n + 1) // j ≠ i} → ℂ => w ⟨j, hji⟩)
      ((ComplexPoints.Analytic.ProjectiveCharts.projectiveAffineChart i).apply_symm_apply z)
    change Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j ((ComplexPoints.Analytic.ProjectiveCharts.projectiveAffineChart i).symm z).val = z ⟨j, hji⟩ at hr
    rw [hr]
    simp only [RatioAwaySection.projectiveRatioAwayElement, Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial_mk,
      Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize_X_of_ne i j hji]
    rfl

theorem projectiveRegularRatio_point_evaluation (n : ℕ) (i j : Fin (n + 1))
    (p : Line.Bundles.AlgebraicLineBundle.analyticOpen (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).presentation (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) :
    Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).presentation (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
      (RegularRatios.projectiveRegularRatio n i j (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) le_rfl) p =
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val) :=
  (projectiveRegularRatio_character_evaluation n i j p).trans (projectiveOpenChartCharacter_ratio n i j p)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RatioPointEvaluation
