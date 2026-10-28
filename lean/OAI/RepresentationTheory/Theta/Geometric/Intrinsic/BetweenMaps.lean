import OAI.RepresentationTheory.Theta.Geometric.Relative.MarkedTransport

/-! # Between Maps -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic

noncomputable section

/-! The actual real and point comparisons between two fibers are the
compositions through their common native central frame. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped Classical

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation Family.FieldActions.familyFieldPeriodAction Family.PELCoordinates.familyPELCoordinates

variable {E : Type} [Field E] [NumberField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : CompatibleTransport.NativeCompatibleTransport A ρ F)

def CompatibleTransport.NativeCompatibleTransport.realBetween (z w : D.neighborhood) :
    AlgebraicAction.AbelianModel (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z)).variety ≃L[ℝ]
      AlgebraicAction.AbelianModel (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C w)).variety :=
  (F.nativeRealTransport z (D.subset_chart z.property)
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)))
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z))).symm.trans
      (F.nativeRealTransport w (D.subset_chart w.property)
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)))
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C w)))

def CompatibleTransport.NativeCompatibleTransport.fiberBetween (z w : D.neighborhood) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z)).variety.toOver ≃ₜ
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C w)).variety.toOver :=
  (F.nativeFiberTransport z (D.subset_frame z.property) (D.subset_chart z.property)
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)))
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z))).symm.trans
      (F.nativeFiberTransport w (D.subset_frame w.property) (D.subset_chart w.property)
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)))
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C w)))

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic
