import OAI.AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionHolomorphy
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions

/-! # Chart Section Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.ChartSectionMap

noncomputable section

/-! The section map induced by the native projective affine chart sends the
original homogeneous fractions to their dehomogenized polynomials. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def projectiveCoordinateSectionMap (n : ℕ) (i : Fin (n + 1)) :
    Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) ⟶ CommRingCat.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i) :=
  (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).topIso.inv ≫ (Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).inv.appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))).hom

@[reassoc]
theorem projectiveAwaySection_inv_chart (n : ℕ) (i : Fin (n + 1)) :
    Proj.awayToSection (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i) ≫
        (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).topIso.inv ≫
        (Proj.basicOpenIsoSpec (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
          (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) (by decide : 0 < 1)).inv.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n i))).inv := by
  apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n i))).hom).mp
  rw [← Category.assoc, ← Category.assoc,
    Category.assoc (Scheme.ΓSpecIso (CommRingCat.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n i))).hom
      (Proj.awayToSection (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i))
      (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).topIso.inv,
    ← Proj.basicOpenToSpec_app_top]
  change (Proj.basicOpenIsoSpec (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
      (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) (by decide : 0 < 1)).hom.appTop ≫
    (Proj.basicOpenIsoSpec (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
      (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) (by decide : 0 < 1)).inv.appTop = _
  rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Iso.hom_inv_id]
  rfl

theorem projectiveCoordinateSectionMap_away (n : ℕ) (i : Fin (n + 1)) :
    Proj.awayToSection (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i) ≫
        projectiveCoordinateSectionMap n i =
      CommRingCat.ofHom (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i) := by
  unfold projectiveCoordinateSectionMap Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec
  rw [Iso.trans_inv, Scheme.Hom.comp_appTop]
  change Proj.awayToSection (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i) ≫
      (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).topIso.inv ≫
      ((Proj.basicOpenIsoSpec (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
        (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) (by decide : 0 < 1)).inv.appTop ≫
        (Spec.map (CommRingCat.ofHom (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i))).appTop) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))).hom = _
  simp only [Category.assoc]
  rw [Scheme.ΓSpecIso_naturality, projectiveAwaySection_inv_chart_assoc, Iso.inv_hom_id_assoc]

theorem projectiveCoordinateSectionMap_localEquation (n : ℕ) (i : Fin (n + 1))
    (j : {j : Fin (n + 1) // j ≠ i}) :
    projectiveCoordinateSectionMap n i (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := ℂ) i j.val) =
      MvPolynomial.X j := by
  rw [SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_of_ne i j.val j.property]
  have h := ConcreteCategory.congr_hom (projectiveCoordinateSectionMap_away n i)
    (SheafCohomology.Projective.SpaceChart.MvPolynomial.awayVar ℂ i j)
  exact h.trans (Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartToPolynomial_ratio n i j)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.ChartSectionMap
