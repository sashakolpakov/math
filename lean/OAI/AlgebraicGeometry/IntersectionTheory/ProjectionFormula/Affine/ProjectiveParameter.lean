import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.ChartFractions
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyIs
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterFiber

/-! # Projective Parameter -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ProjectiveParameter

noncomputable section

/-! The regular projective-line parameter on its standard affine
chart is exactly the polynomial coordinate in the native stalk. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Polynomial

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyIs.MatrixParameterOpen

theorem contained (x : Spec (.of ℂ[X])) : Projective.FamilyIs.MatrixParameterOpen.affine x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0 :=
  ProjectionFormula.Polynomial.ChartFractions.contained 1 0
    (Spec.map (CommRingCat.ofHom Projective.FamilyIs.MatrixParameterOpen.chartEquiv.toRingHom) x)

theorem polynomial : Projective.FamilyIs.MatrixParameterOpen.chartEquiv
    (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize (0 : Fin 2)
      (Projective.LineParameter.RationalFractions.coordinate 1 1).val) = Polynomial.X := by
  simp [Projective.LineParameter.RationalFractions.coordinate, Projective.FamilyIs.MatrixParameterOpen.chartEquiv,
    Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize_X_of_ne]

theorem finiteGerm (x : Spec (.of ℂ[X])) :
    Projective.ParameterGerms.finiteGerm Projective.FamilyIs.MatrixParameterOpen.affine x (contained x) =
      StructureSheaf.toStalk ℂ[X] x Polynomial.X := by
  change GermPullback.fraction 1
    (Spec.map (CommRingCat.ofHom Projective.FamilyIs.MatrixParameterOpen.chartEquiv.toRingHom) ≫ Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap 1 0) x
      (Projective.LineParameter.RationalFractions.coordinate 1 1)
      (Projective.LineParameter.RationalFractions.coordinate 1 0) (contained x) = _
  rw [GermPullback.fraction_comp, ProjectionFormula.Polynomial.ChartFractions.fraction]
  exact (Projection.ChartFractions.spec_germ (CommRingCat.ofHom Projective.FamilyIs.MatrixParameterOpen.chartEquiv.toRingHom) x
    (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize (0 : Fin 2)
      (Projective.LineParameter.RationalFractions.coordinate 1 1).val)).trans
        (congrArg (StructureSheaf.toStalk ℂ[X] x) polynomial)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ProjectiveParameter
