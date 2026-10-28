import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CompatibleTransport
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FrameRationalEquiv

/-! # Compatible Field Equiv -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The constructed original rational transport is linear over the
entire given field action and preserves the original polarization form. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation PolarizedCanonicalForm.familyPolarizationForm Family.FieldActions.familyFieldPeriodAction

variable {E : Type} [Field E] [NumberField E] {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

abbrev CompatibleFieldEquiv.familyPeriodFieldModule (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    Module E (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A y).variety) :=
  Module.compHom _ (Family.FieldActions.familyFieldPeriodAction A ρ y).toRingHom

variable {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F)

def Intrinsic.CompatibleTransport.NativeCompatibleTransport.fieldEquiv (z : D.neighborhood) :
    let P₀ := PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))
    let P := PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)
    let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))
    let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C z)
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods P₀.variety ≃ₗ[E] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods P.variety := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C z)
  let e := F.nativeRationalEquiv z (D.subset_frame z.property) (D.subset_chart z.property)
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z))
  let f : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))).variety →ₗ[E]
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety := {
    toFun := e
    map_add' := e.map_add
    map_smul' := by
      intro a v
      change e (Family.FieldActions.familyFieldPeriodAction A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) a v) =
        Family.FieldActions.familyFieldPeriodAction A ρ (Intrinsic.FamilyFrames.familyChartParameter C z) a (e v)
      exact (D.field z a v).symm }
  exact LinearEquiv.ofBijective f e.bijective

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.fieldEquiv_apply (z : D.neighborhood)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))).variety) :
    D.fieldEquiv A ρ z v = F.nativeRationalTransport z (D.subset_frame z.property) (D.subset_chart z.property)
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)) v := rfl

end

end OAI.RepresentationTheory.Theta.Geometric
