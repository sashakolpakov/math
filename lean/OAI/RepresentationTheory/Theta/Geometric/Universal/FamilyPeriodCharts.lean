import OAI.RepresentationTheory.Theta.Geometric.Complex.FamilyPresentation
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts
import OAI.RepresentationTheory.Theta.Geometric.Period.PointsIntrinsicFamilyMatrices

/-! # Family Period Charts -/

namespace OAI.RepresentationTheory.Theta.Geometric.Universal.FamilyPeriodCharts

noncomputable section

/-! Local holomorphic full period matrices for the original universal
PEL family on any smooth integral complex base mapping to the moduli space. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ D.complexSpace) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)

def complexUniversalFamilyCharts : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts (Complex.PELClassification.complexUniversalFamily D f).abelian x :=
  Classical.choice (AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.exists_native_family_charts (Complex.PELClassification.complexUniversalFamily D f).abelian x)

theorem complexUniversalFamilyCharts_dimension :
    let C := complexUniversalFamilyCharts D f x
    Module.finrank ℂ (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates C.presentation.presentation.map → ℂ) =
      AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom :=
  (complexUniversalFamilyCharts D f x).dimension

theorem exists_complexUniversal_holomorphic_period_matrices :
    let C := complexUniversalFamilyCharts D f x
    let B := AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates C.presentation.presentation.map → ℂ
    let N := C.charts.charts
    let parameter := fun z : B => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap C.algebra C.openMap (N.charts.base.symm z)
    ∃ (n d : ℕ) (U : Set B), IsOpen U ∧ N.charts.base C.point ∈ U ∧ U ⊆ N.neighborhood ∧
      ∃ (marking : ∀ z : U, ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Fin n)
          (Complex.FamilyPresentation.complexUniversalFiberPresentation D hg f (parameter z)).variety)
        (coordinates : ∀ z : U, AlgebraicAction.AbelianModel (Complex.FamilyPresentation.complexUniversalFiberPresentation D hg f (parameter z)).variety ≃L[ℂ]
          (Fin d → ℂ))
        (matrix : B → (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)),
        DifferentiableOn ℂ matrix U ∧
        (∀ z : U, matrix z = ((coordinates z).toLinearEquiv.toLinearMap.comp
          (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (marking z))).toContinuousLinearMap) ∧
        (∀ z : U, Function.Surjective (matrix z)) ∧
        ∀ z : U, (matrix z).ker = (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (marking z)).ker := by
  let C := complexUniversalFamilyCharts D f x
  let V := AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates C.charts.relativePresentation.presentation.map → ℂ
  let B := AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates C.presentation.presentation.map → ℂ
  obtain ⟨n, d, U, hU, hcenter, hsub, marking, coordinates, matrix, hhol, hm, hsurj, hker⟩ :=
    AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyPeriodMatrices.exists_native_family_holomorphic_period_matrices (E := V) (F := B)
    (Complex.PELClassification.complexUniversalFamily D f).abelian (Complex.FamilyPresentation.complexUniversalFiberPresentation D hg f)
    C.charts.affineOpen C.charts.isAffine C.openMap C.charts.projection_eq
    C.charts.sectionAlgebra C.charts.section_eq C.charts.charts
  have hx : C.charts.charts.charts.base C.point ∈ U := by
    simpa only [AlgHom.comp_assoc, C.charts.retraction, AlgHom.comp_id] using hcenter
  exact ⟨n, d, U, hU, hx, hsub, marking, coordinates, matrix, hhol, hm, hsurj, hker⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Universal.FamilyPeriodCharts
