import OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechLaurentPoints
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechRingHomExt
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechLaurentRestriction
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ChartEvaluation

/-! # Cech Regular Laurent Evaluation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechRegularLaurentEvaluation.Dolbeault

noncomputable section

/-! Original regular evaluation on each projective intersection equals its Laurent polynomial evaluation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates _root_.MvPolynomial

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace Algebraic.Sheaves.sectionAlgebra

def projectiveCechPointOnFirstChart (n q : ℕ) (a : Fin (q + 1) → ULift.{0} (Fin (n + 1)))
    (p : CechLaurentPoints.Dolbeault.projectiveCechAnalyticPoints n q a) :
    Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n (a 0).down) :=
  ⟨p.val, Open.SmoothForms.analyticOpen_mono (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := ℂ) a 0) p.property⟩

theorem projectiveCechRegularEvaluation_restrict (n q : ℕ)
    (a : Fin (q + 1) → ULift.{0} (Fin (n + 1))) (p : CechLaurentPoints.Dolbeault.projectiveCechAnalyticPoints n q a)
    (s : Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n (a 0).down)) :
    CechLaurentPoints.Dolbeault.projectiveCechRegularEvaluation n q a p
      ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.map (homOfLE (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := ℂ) a 0)).op s) =
      MvPolynomial.eval (CechLaurentPoints.Dolbeault.projectiveCechChartCoordinates n q a p)
        (ChartSectionMap.projectiveCoordinateSectionMap n (a 0).down s) := by
  have hr := Open.AffineIsoEvaluation.sectionEvaluationOn_restrict (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := ℂ) a 0) s p
  exact hr.trans (ChartEvaluation.Dolbeault.projectiveChartSection_evaluation n (a 0).down
    (projectiveCechPointOnFirstChart n q a p) s)

def projectiveCechFirstChartSection (n q : ℕ) (a : Fin (q + 1) → ULift.{0} (Fin (n + 1)))
    (b : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n (a 0).down) :
    Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n (a 0).down) :=
  (Proj.basicOpenIsoAway (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (X (a 0).down)
    (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n (a 0).down) one_pos).hom b

theorem projectiveCechFirstChartSection_polynomial (n q : ℕ)
    (a : Fin (q + 1) → ULift.{0} (Fin (n + 1))) (b : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n (a 0).down) :
    ChartSectionMap.projectiveCoordinateSectionMap n (a 0).down (projectiveCechFirstChartSection n q a b) =
      @SheafCohomology.Projective.SpaceChart.MvPolynomial.chartRingEquiv ℂ (Fin (n + 1)) _ (Classical.decEq _) (a 0).down b := by
  have h := ConcreteCategory.congr_hom (ChartSectionMap.projectiveCoordinateSectionMap_away n (a 0).down) b
  change ChartSectionMap.projectiveCoordinateSectionMap n (a 0).down (projectiveCechFirstChartSection n q a b) =
    Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n (a 0).down b at h
  exact h.trans (ChartEvaluation.Dolbeault.projectiveChartToPolynomial_eq_laurentChart_with_decidable
    n (a 0).down (Classical.decEq _) b)

theorem projectiveCechLaurentEvaluation_restrict (n q : ℕ)
    (a : Fin (q + 1) → ULift.{0} (Fin (n + 1))) (p : CechLaurentPoints.Dolbeault.projectiveCechAnalyticPoints n q a)
    (b : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n (a 0).down) :
    CechLaurentPoints.Dolbeault.projectiveCechLaurentEvaluation n q a p
      ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.map (homOfLE (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := ℂ) a 0)).op
        (projectiveCechFirstChartSection n q a b)) =
      MvPolynomial.eval (CechLaurentPoints.Dolbeault.projectiveCechChartCoordinates n q a p)
        (@SheafCohomology.Projective.SpaceChart.MvPolynomial.chartRingEquiv ℂ (Fin (n + 1)) _ (Classical.decEq _) (a 0).down b) := by
  let F := Laurent.MonomialEvaluation.Dolbeault.allowedLaurentEvaluation (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a k).down))
    (CechLaurentPoints.Dolbeault.projectiveCechChartCoordinates n q a p) (CechLaurentPoints.Dolbeault.projectiveCechChartCoordinates_allowed n q a p)
  exact (congrArg F (CechLaurentRestriction.Dolbeault.projectiveCechLaurent_restrict_firstChart a b)).trans
    (Laurent.MonomialEvaluation.Dolbeault.allowedLaurentEvaluation_polynomial _ _ _ _)

theorem projectiveCechRegularEvaluation_eq_laurentEvaluation (n q : ℕ)
    (a : Fin (q + 1) → ULift.{0} (Fin (n + 1))) (p : CechLaurentPoints.Dolbeault.projectiveCechAnalyticPoints n q a) :
    CechLaurentPoints.Dolbeault.projectiveCechRegularEvaluation n q a p = CechLaurentPoints.Dolbeault.projectiveCechLaurentEvaluation n q a p := by
  apply CechRingHomExt.Dolbeault.projectiveCechRingHom_ext_firstChart a
  intro s
  let e := Proj.basicOpenIsoAway (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (X (a 0).down)
    (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n (a 0).down) one_pos
  obtain ⟨b, rfl⟩ := e.commRingCatIsoToRingEquiv.surjective s
  exact (projectiveCechRegularEvaluation_restrict n q a p (projectiveCechFirstChartSection n q a b)).trans
    ((congrArg (MvPolynomial.eval (CechLaurentPoints.Dolbeault.projectiveCechChartCoordinates n q a p))
      (projectiveCechFirstChartSection_polynomial n q a b)).trans
        (projectiveCechLaurentEvaluation_restrict n q a p b).symm)

theorem projectiveCechRegularSection_laurentEvaluation (n q : ℕ)
    (a : Fin (q + 1) → ULift.{0} (Fin (n + 1))) (p : CechLaurentPoints.Dolbeault.projectiveCechAnalyticPoints n q a)
    (s : Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := ℂ) a)) :
    Holomorphic.RegularSections.regularHolomorphicSectionMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
      (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := ℂ) a) s p =
      Laurent.MonomialEvaluation.Dolbeault.allowedLaurentEvaluation (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a k).down))
        (CechLaurentPoints.Dolbeault.projectiveCechChartCoordinates n q a p) (CechLaurentPoints.Dolbeault.projectiveCechChartCoordinates_allowed n q a p)
        (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv (R := ℂ) a s) :=
  DFunLike.congr_fun (projectiveCechRegularEvaluation_eq_laurentEvaluation n q a p) s

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechRegularLaurentEvaluation.Dolbeault
