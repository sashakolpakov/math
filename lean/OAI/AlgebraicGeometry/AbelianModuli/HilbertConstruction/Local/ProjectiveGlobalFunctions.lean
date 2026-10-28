import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GlobalFunctionsIdentityModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.ConnectedFieldCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.MatrixAlgebraModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.CoefficientRetraction

/-! # Projective Global Functions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProjectiveGlobalFunctions

noncomputable section

/-! Global regular functions on a pointed proper smooth geometrically connected projective coordinate family over a noetherian local ring are exactly the base ring, including over nonreduced bases. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem localPointedProjectiveCoordinate_globalFunctions_isIso
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    [IsProper (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
    [Smooth (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
    [GeometricallyConnected (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
    (x : Spec (.of R) ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
    (hx : x ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) = 𝟙 _) :
    IsIso (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).appTop := by
  obtain ⟨m, k, B, hI, hB⟩ := Projective.GlobalFunctionsIdentityModel.flatProjectiveCoordinate_globalFunctions_uniform_matrix_with_identity I
  let K := IsLocalRing.ResidueField R
  have hd : Module.finrank K (Matrix.toLin' (B.map (algebraMap R K))).ker ≤ 1 :=
    (ProjectiveCoordinate.ConnectedFieldCriterion.projectiveCoordinate_connected_field_kernel I x hx B (Classical.choice (hB K))).mp inferInstance
  let p := HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
  let σ := Section.CoefficientRetraction.sectionCoefficientRetraction p x hx
  have H := MatrixAlgebraModel.localMatrixModel_algebraMap_bijective B (Classical.choice hI) σ.toLinearMap σ.map_one hd
  change Function.Bijective (Coefficient.AlgebraPresheaf.coefficientSectionMap (Affine.ChartCoefficientSections.schemeGlobalCoefficient p) ⊤) at H
  rw [Coefficient.GlobalFunctionDimension.coefficientSectionMap_top] at H
  exact (ConcreteCategory.isIso_iff_bijective p.appTop).mpr ((Coefficient.GlobalFunctionDimension.schemeGlobalCoefficient_bijective_iff p).mp H)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProjectiveGlobalFunctions
