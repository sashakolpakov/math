import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RatioAwaySection
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart

/-! # Chart Section Map -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ChartSectionMap

noncomputable section

/-! The native affine coordinate chart induces the explicit map on regular sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem projectiveCoordinateIsoSpec_sections (n : ℕ) (i : Fin (n + 1)) :
    (Scheme.ΓSpecIso (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))).inv ≫
        (Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).hom.appTop =
      CommRingCat.ofHom (Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv n i).symm.toRingHom ≫
        Proj.awayToSection (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i) ≫
        (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).topIso.inv := by
  have he : (Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).hom =
      (Proj.basicOpenIsoSpec (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
        (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) (by decide : 0 < 1)).hom ≫
      Spec.map (CommRingCat.ofHom (Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv n i).symm.toRingHom) := rfl
  rw [he, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Proj.basicOpenIsoSpec_hom]
  dsimp only [Scheme.Hom.appTop]
  rw [Proj.basicOpenToSpec_app_top (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

theorem projectiveCoordinateIsoSpec_ratio_section (n : ℕ) (i j : Fin (n + 1)) :
    (Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).hom.appTop
        ((Scheme.ΓSpecIso (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))).inv
          (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i (RatioAwaySection.projectiveRatioAwayElement n i j))) =
      (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).topIso.inv
        (RegularRatios.projectiveRegularRatio n i j (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) le_rfl) := by
  have h := ConcreteCategory.congr_hom (projectiveCoordinateIsoSpec_sections n i)
    (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i (RatioAwaySection.projectiveRatioAwayElement n i j))
  change _ = (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).topIso.inv
    (Proj.awayToSection (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
      ((Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv n i).symm
        ((Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv n i) (RatioAwaySection.projectiveRatioAwayElement n i j)))) at h
  rw [RingEquiv.symm_apply_apply, ← RatioAwaySection.projectiveRegularRatio_eq_awayToSection] at h
  exact h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ChartSectionMap
