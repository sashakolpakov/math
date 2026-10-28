import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.BetweenMaps
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.RationalInverse

/-! # Between Rational Values -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic

noncomputable section

/-! The actual real and point transports between two fibers retain
their original rational map and every original full-level label. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped Classical

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation Family.FieldActions.familyFieldPeriodAction Family.PELCoordinates.familyPELCoordinates
  FamilyFrames.NativeFamilyPeriodFrame.nativeRealTransport FamilyFrames.NativeFamilyPeriodFrame.nativeRationalEquiv
  FamilyFrames.NativeFamilyPeriodFrame.nativeFiberTransport

variable {E : Type} [Field E] [NumberField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : CompatibleTransport.NativeCompatibleTransport A ρ F)

theorem CompatibleTransport.NativeCompatibleTransport.rationalBetween_coe (z w : D.neighborhood)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z)).variety) :
    (D.rationalBetween A ρ z w v).val = D.realBetween A ρ z w v.val := by
  let P₀ := PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C))
  let Pz := PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z)
  let Pw := PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C w)
  let t := F.nativeRationalEquiv z (D.subset_frame z.property) (D.subset_chart z.property) P₀ Pz
  exact (F.nativeRationalEquiv_coe w (D.subset_frame w.property) (D.subset_chart w.property) P₀ Pw (t.symm v)).trans
    (congrArg (F.nativeRealTransport w (D.subset_chart w.property) P₀ Pw)
      (F.nativeRationalEquiv_symm_coe z (D.subset_frame z.property) (D.subset_chart z.property) P₀ Pz v))

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic
