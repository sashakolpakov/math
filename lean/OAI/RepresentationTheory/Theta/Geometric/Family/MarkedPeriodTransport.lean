import OAI.RepresentationTheory.Theta.Geometric.Family.PELCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PeriodTransport

/-! # Marked Period Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The existing marked-period construction recovers exactly the
constructed rational transport of the actual family. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PeriodTransport.IntrinsicPELMarking

attribute [local irreducible] Family.FieldActions.familyFieldPeriodAction

variable {E : Type} [Field E] [NumberField E] {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.markedPeriodTransport_eq (z : D.neighborhood)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))).variety) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)).left)
      (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)).left))
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left))
      (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)).left)
      (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left) s hs hg hdegree
      (D.coordinateTransport A ρ s hs hg hdegree z) v =
      F.nativeRationalTransport z (D.subset_frame z.property) (D.subset_chart z.property)
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)) v := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C z)
  let c₀ := Family.PELCoordinates.familyPELCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree
  let c := Family.PELCoordinates.familyPELCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree
  change c.symm (c (D.fieldEquiv A ρ z (c₀.symm (c₀ v)))) = _
  rw [c₀.symm_apply_apply, c.symm_apply_apply]
  exact D.fieldEquiv_apply A ρ z v

end

end OAI.RepresentationTheory.Theta.Geometric
