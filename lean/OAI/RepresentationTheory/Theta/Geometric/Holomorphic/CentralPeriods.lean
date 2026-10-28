import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.HolomorphicTransport
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FrameRationalEquiv
import OAI.RepresentationTheory.Theta.Geometric.MarkingComplexTransport

/-! # Central Periods -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The constructed holomorphic matrices are the actual native period
projections expressed in the fixed central rational marking. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation PolarizedCanonicalForm.familyPolarizationForm Family.FieldActions.familyFieldPeriodAction

variable {E : Type} [Field E] [NumberField E] {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left}
    {ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (H : Intrinsic.HolomorphicTransport.NativeHolomorphicTransport A ρ F)

abbrev Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.centralMarking := H.marking ⟨Intrinsic.FamilyFrames.familyChartCenter C, H.compatible.center⟩

def Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.rationalTransport (z : H.compatible.neighborhood) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))).variety ≃ₗ[ℚ]
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety :=
  F.nativeRationalEquiv z (H.compatible.subset_frame z.property) (H.compatible.subset_chart z.property)
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z))

theorem Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.rationalTransport_marking (z : H.compatible.neighborhood) (i : Fin F.rank) :
    H.rationalTransport z (MarkingComplexTransport.markingRationalBasis H.centralMarking i) =
      MarkingComplexTransport.markingRationalBasis (H.marking z) i := by
  apply Subtype.ext
  change F.nativeRealTransport z (H.compatible.subset_chart z.property)
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z))
    (MarkingComplexTransport.markingRationalBasis H.centralMarking i).val = (MarkingComplexTransport.markingRationalBasis (H.marking z) i).val
  rw [MarkingComplexTransport.markingRationalBasis_coe, MarkingComplexTransport.markingRationalBasis_coe]
  exact H.marking_transport z i

theorem Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.complexProjection_transport (z : H.compatible.neighborhood)
    (u : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))).variety)) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety
      ((H.rationalTransport z).toLinearMap.baseChange ℂ u) =
      ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (H.marking z) ((MarkingComplexTransport.markingComplexBasis H.centralMarking).equivFun u) :=
  MarkingComplexTransport.complexPeriodProjection_transport_marking H.centralMarking (H.marking z)
    (H.rationalTransport z).toLinearMap (H.rationalTransport_marking z) u

theorem Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.matrix_central_projection (z : H.compatible.neighborhood)
    (u : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))).variety)) :
    H.matrix z ((MarkingComplexTransport.markingComplexBasis H.centralMarking).equivFun u) =
      ((H.tangentCoordinates z).symm.trans H.coordinates)
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety
          ((H.rationalTransport z).toLinearMap.baseChange ℂ u)) := by
  rw [H.matrix_eq, H.complexProjection_transport]
  rfl

theorem Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.matrix_kernel_iff (z : H.compatible.neighborhood)
    (u : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))).variety)) :
    H.matrix z ((MarkingComplexTransport.markingComplexBasis H.centralMarking).equivFun u) = 0 ↔
      (H.rationalTransport z).toLinearMap.baseChange ℂ u ∈
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety).ker := by
  rw [H.matrix_central_projection]
  exact ((H.tangentCoordinates z).symm.trans H.coordinates).map_eq_zero_iff

end

end OAI.RepresentationTheory.Theta.Geometric
