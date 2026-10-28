import OAI.RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking

/-! # PEL Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Actual rank-three field coordinates of the fibers, and the coordinate
change induced by the constructed common rational transport. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking

variable {E : Type} [Field E] [NumberField E] {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

abbrev Family.PELCoordinates.familyPeriodScalarTower (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ y
    IsScalarTower ℚ E (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A y).variety) :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower (A.abelian.pullback y.left)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback y.left)) (ρ.pullback y.left)

def Family.PELCoordinates.familyPELCoordinates (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (s : ℕ) (hs : 0 < s)
    (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s) :
    let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ y
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A y).variety ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates (A.abelian.pullback y.left) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback y.left))
    (ρ.pullback y.left) s hs hg hdegree

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation Family.FieldActions.familyFieldPeriodAction Family.PELCoordinates.familyPELCoordinates

variable {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

def Intrinsic.CompatibleTransport.NativeCompatibleTransport.coordinateTransport (z : D.neighborhood) : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C z)
  exact (Family.PELCoordinates.familyPELCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree).symm.trans
    ((D.fieldEquiv A ρ z).trans (Family.PELCoordinates.familyPELCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree))

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.coordinateTransport_apply (z : D.neighborhood)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))).variety) :
    D.coordinateTransport A ρ s hs hg hdegree z
      (Family.PELCoordinates.familyPELCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree v) =
      Family.PELCoordinates.familyPELCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree
        (F.nativeRationalTransport z (D.subset_frame z.property) (D.subset_chart z.property)
          (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
          (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)) v) := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C z)
  change Family.PELCoordinates.familyPELCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree
    (D.fieldEquiv A ρ z ((Family.PELCoordinates.familyPELCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree).symm
      (Family.PELCoordinates.familyPELCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree v))) = _
  rw [LinearEquiv.symm_apply_apply, D.fieldEquiv_apply]

end

end OAI.RepresentationTheory.Theta.Geometric
