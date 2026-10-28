import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTransport
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FrameRationalEquiv
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.MarkingCoordinates

/-! # Central Periods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The constructed holomorphic matrices are the actual native period
projections expressed in the fixed central rational marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FrameRationalEquiv

attribute [local irreducible] RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm RepresentationTheory.Theta.Geometric.Family.FieldActions.familyFieldPeriodAction

variable {E : Type} [Field E] [NumberField E] {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    {A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left}
    {ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian}
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport A ρ F)

abbrev Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.centralMarking := H.marking ⟨RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C, H.compatible.center⟩

def Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.rationalTransport (z : H.compatible.neighborhood) :
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C))).variety ≃ₗ[ℚ]
      Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety :=
  F.nativeRationalEquiv z (H.compatible.subset_frame z.property) (H.compatible.subset_chart z.property)
    (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)))
    (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z))

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.rationalTransport_marking (z : H.compatible.neighborhood) (i : Fin F.rank) :
    H.rationalTransport z (Family.MarkingCoordinates.markingRationalBasis H.centralMarking i) =
      Family.MarkingCoordinates.markingRationalBasis (H.marking z) i := by
  apply Subtype.ext
  change F.nativeRealTransport z (H.compatible.subset_chart z.property)
    (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)))
    (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z))
    (Family.MarkingCoordinates.markingRationalBasis H.centralMarking i).val = (Family.MarkingCoordinates.markingRationalBasis (H.marking z) i).val
  rw [Family.MarkingCoordinates.markingRationalBasis_coe, Family.MarkingCoordinates.markingRationalBasis_coe]
  exact H.marking_transport z i

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.complexProjection_transport (z : H.compatible.neighborhood)
    (u : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods
      (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C))).variety)) :
    Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety
      ((H.rationalTransport z).toLinearMap.baseChange ℂ u) =
      ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (H.marking z) ((Family.MarkingCoordinates.markingComplexBasis H.centralMarking).equivFun u) :=
  Family.MarkingCoordinates.complexPeriodProjection_transport_marking H.centralMarking (H.marking z)
    (H.rationalTransport z).toLinearMap (H.rationalTransport_marking z) u

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.matrix_central_projection (z : H.compatible.neighborhood)
    (u : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods
      (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C))).variety)) :
    H.matrix z ((Family.MarkingCoordinates.markingComplexBasis H.centralMarking).equivFun u) =
      ((H.tangentCoordinates z).symm.trans H.coordinates)
        (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety
          ((H.rationalTransport z).toLinearMap.baseChange ℂ u)) := by
  rw [H.matrix_eq, H.complexProjection_transport]
  rfl

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.matrix_kernel_iff (z : H.compatible.neighborhood)
    (u : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods
      (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C))).variety)) :
    H.matrix z ((Family.MarkingCoordinates.markingComplexBasis H.centralMarking).equivFun u) = 0 ↔
      (H.rationalTransport z).toLinearMap.baseChange ℂ u ∈
        (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety).ker := by
  rw [H.matrix_central_projection]
  exact ((H.tangentCoordinates z).symm.trans H.coordinates).map_eq_zero_iff

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
