import OAI.RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm
import OAI.RepresentationTheory.Theta.Geometric.PresentedFrameEndomorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction

/-! # Field Actions -/

namespace OAI.RepresentationTheory.Theta.Geometric.Family.FieldActions

noncomputable section

section

/-! The original integral CM action and its canonical full field
extension on the actual presented rational periods of each family fiber. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction

variable {E : Type} [Field E] [NumberField E] {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

def familyIntegralPeriodAction (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    NumberField.RingOfIntegers E →+* Module.End ℚ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A y).variety) :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction (A.abelian.pullback y.left) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback y.left))
    (ρ.pullback y.left)

def familyFieldPeriodAction (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    E →ₐ[ℚ] Module.End ℚ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A y).variety) :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction (A.abelian.pullback y.left) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback y.left))
    (ρ.pullback y.left)

theorem familyFieldPeriodAction_integer (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (a : NumberField.RingOfIntegers E)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A y).variety) :
    familyFieldPeriodAction A ρ y (a : E) v = familyIntegralPeriodAction A ρ y a v :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction_integer_apply _ _ _ a v

omit [NumberField E] in
theorem familyIntegralPeriodAction_frame {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    (C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x) (z : Intrinsic.FamilyFrames.FamilyChartBase C) (a : NumberField.RingOfIntegers E) :
    familyIntegralPeriodAction A ρ (Intrinsic.FamilyFrames.familyChartParameter C z) a =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism (C := C) z
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)) (ρ.map a)) := rfl

end

/-! The original integral action on a family fiber is exactly the
rational lift of its literal conjugate through the native presentation. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem familyIntegralPeriodAction_presented {E : Type} [Field E] [NumberField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (a : NumberField.RingOfIntegers E) :
    familyIntegralPeriodAction A ρ x a = AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift
      ((PolarizedCanonicalForm.polarizedFamilyPresentation A x).comparison.inv ≫ (ρ.pullback x.left).map a ≫
        (PolarizedCanonicalForm.polarizedFamilyPresentation A x).comparison.hom) := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.Family.FieldActions
