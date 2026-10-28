import OAI.RepresentationTheory.Theta.Geometric.Relative.MarkedTransport
import OAI.RepresentationTheory.Theta.Geometric.Family.PELCoordinates

/-! # Field Equiv -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! The comparison through the common center intertwines the entire
original field action and hence every original integral endomorphism. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation Family.FieldActions.familyFieldPeriodAction Family.PELCoordinates.familyPELCoordinates

variable {E : Type} [Field E] [NumberField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.rationalBetween_field (z w : D.neighborhood) (a : E)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety) :
    Family.FieldActions.familyFieldPeriodAction A ρ (Intrinsic.FamilyFrames.familyChartParameter C w) a (D.rationalBetween A ρ z w v) =
      D.rationalBetween A ρ z w (Family.FieldActions.familyFieldPeriodAction A ρ (Intrinsic.FamilyFrames.familyChartParameter C z) a v) := by
  obtain ⟨v₀, rfl⟩ := (F.nativeRationalEquiv z (D.subset_frame z.property) (D.subset_chart z.property)
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z))).surjective v
  have hl := congrArg (Family.FieldActions.familyFieldPeriodAction A ρ (Intrinsic.FamilyFrames.familyChartParameter C w) a)
    (D.rationalBetween_apply_center A ρ z w v₀)
  have hr := (congrArg (D.rationalBetween A ρ z w) (D.field z a v₀)).trans
    (D.rationalBetween_apply_center A ρ z w
      (Family.FieldActions.familyFieldPeriodAction A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) a v₀))
  exact hl.trans ((D.field w a v₀).trans hr.symm)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.rationalBetween_integer (z w : D.neighborhood) (a : NumberField.RingOfIntegers E)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety) :
    Family.FieldActions.familyIntegralPeriodAction A ρ (Intrinsic.FamilyFrames.familyChartParameter C w) a (D.rationalBetween A ρ z w v) =
      D.rationalBetween A ρ z w (Family.FieldActions.familyIntegralPeriodAction A ρ (Intrinsic.FamilyFrames.familyChartParameter C z) a v) :=
  (Family.FieldActions.familyFieldPeriodAction_integer A ρ (Intrinsic.FamilyFrames.familyChartParameter C w) a (D.rationalBetween A ρ z w v)).symm.trans
    ((D.rationalBetween_field A ρ z w (a : E) v).trans
      (congrArg (D.rationalBetween A ρ z w) (Family.FieldActions.familyFieldPeriodAction_integer A ρ (Intrinsic.FamilyFrames.familyChartParameter C z) a v)))

end

/-! The actual rational comparison between two compatible fibers is
a linear equivalence over their original full field actions. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F)

def Intrinsic.CompatibleTransport.NativeCompatibleTransport.fieldBetween (z w : D.neighborhood) :
    let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C z)
    let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C w)
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety ≃ₗ[E]
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w)).variety := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C z)
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C w)
  let e := D.rationalBetween A ρ z w
  let m : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety →ₗ[E]
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w)).variety := {
    toFun := e
    map_add' := e.map_add
    map_smul' := fun a v => (D.rationalBetween_field A ρ z w a v).symm }
  exact LinearEquiv.ofBijective m e.bijective

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.fieldBetween_apply (z w : D.neighborhood)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety) :
    D.fieldBetween A ρ z w v = D.rationalBetween A ρ z w v := rfl

end

end OAI.RepresentationTheory.Theta.Geometric
