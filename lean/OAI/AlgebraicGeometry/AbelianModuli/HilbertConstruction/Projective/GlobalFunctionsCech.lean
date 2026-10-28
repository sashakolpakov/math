import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechChartAgreement
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberwiseModuleCech

/-! # Global Functions Cech -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GlobalFunctionsCech

noncomputable section

/-! Actual global regular functions on a projective coordinate quotient are its degree-zero coordinate Čech sections, linearly over the coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberwiseModuleCech.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateCompatibleSectionsCechEquiv :
    Module.SheafOverlapEquivalence.compatibleOpenSectionModule
      (AlgebraSectionModules.algebraSectionModulePresheaf (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))))
      (fun i : Fin (n + 1) => ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) ≃ₗ[R]
    HilbertScheme.Presentations.FiberwiseModuleCech.ProjectiveCech.moduleCechSections (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0 := by
  let F := AlgebraSectionModules.algebraSectionModulePresheaf (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
  let U := fun i : Fin (n + 1) => ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}
  let e : ((i : Fin (n + 1)) → F.obj (op (U i))) ≃ₗ[R]
      HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0 1 :=
    ProjectiveCoordinate.Cover.coordinateChartTupleCechEquiv I
  refine e.ofSubmodules (Module.SheafOverlapEquivalence.compatibleOpenSectionModule F U)
    (HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
      (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0 1).ker ?_
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (CechChartAgreement.coordinateChartTupleCechEquiv_kernel_iff I x).mpr hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    exact (CechChartAgreement.coordinateChartTupleCechEquiv_kernel_iff I (e.symm y)).mp
      ((e.apply_symm_apply y).symm ▸ hy)

def coordinateGlobalFunctionsCechEquiv :
    Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) ⊤ ≃ₗ[R]
      HilbertScheme.Presentations.FiberwiseModuleCech.ProjectiveCech.moduleCechSections (σ := Fin (n + 1)) R
        (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0 :=
  (Module.SheafOverlapEquivalence.globalOpenSectionEquiv
    (AlgebraSectionModules.algebraSectionModulePresheaf (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))))
    (fun i : Fin (n + 1) => ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})
    (AlgebraSectionModules.algebraSectionModulePresheaf_isSheaf _) (ProjectiveCoordinate.Cover.coordinateProjectiveChartOpen_cover I)).trans
      (coordinateCompatibleSectionsCechEquiv I)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GlobalFunctionsCech
