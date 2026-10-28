import OAI.RepresentationTheory.Theta.Geometric.Relative.PolarizedHodgeIso
import OAI.RepresentationTheory.Theta.Geometric.Relative.FieldEquiv

/-! # Hodge Action -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The algebraized comparison intertwines every original integral
PEL endomorphism as an equality of actual scheme morphisms. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local irreducible] Intrinsic.CompatibleTransport.NativeCompatibleTransport.polarizedIso

variable {E : Type} [Field E] [NumberField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F) (z w : D.neighborhood)
    (hH : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety)
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w)).variety)
      (D.rationalBetween A ρ z w).toLinearMap)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.polarizedIso_action (a : NumberField.RingOfIntegers E) :
    (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left).map a ≫ (D.polarizedIso A ρ z w hH).hom =
      (D.polarizedIso A ρ z w hH).hom ≫ (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left).map a := by
  unfold Intrinsic.CompatibleTransport.NativeCompatibleTransport.polarizedIso AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.HodgeAlgebraization.polarizedHodgeAbelianIso
  apply AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.HodgeIso.AbelianIntrinsicAdapter.originalHodgeIso_intertwines
    (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left) (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left))
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left))
    (D.rationalBetween A ρ z w) hH (AlgebraicGeometry.AbelianModuli.ReferenceFamily.HodgeInverse.isHodgeMap_inverse _ _ (D.rationalBetween A ρ z w) hH)
    (fun v => (D.rationalBetween_integral A ρ z w v).symm)
    (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left) (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left) ?_ a
  intro b
  apply LinearMap.ext
  intro v
  exact (D.rationalBetween_integer A ρ z w b v).symm

end

end OAI.RepresentationTheory.Theta.Geometric
