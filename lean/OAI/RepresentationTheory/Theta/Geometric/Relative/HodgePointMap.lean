import OAI.RepresentationTheory.Theta.Geometric.Relative.PolarizedHodgeIso
import OAI.RepresentationTheory.Theta.Geometric.Relative.IntrinsicPeriodSquare
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.AlgebraicTransportComparison

/-! # Hodge Point Map -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The algebraized original Hodge isomorphism induces exactly the
already constructed native fiber homeomorphism on every complex point. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

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

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.polarizedIso_native_points :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
      ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left))).hom ≫
        (D.polarizedIso A ρ z w hH).hom ≫
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left)
          (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left))).inv) =
      D.fiberBetween A ρ z w := by
  let : IsMonHom (D.polarizedIso A ρ z w hH).hom := D.polarizedIso_group A ρ z w hH
  let f := (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left))).hom ≫
    (D.polarizedIso A ρ z w hH).hom ≫
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left)
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left))).inv
  let : IsMonHom f := inferInstance
  apply Intrinsic.AlgebraicTransportComparison.RealPeriodMaps.algebraicPointMap_eq_of_rational_transport f
    (D.realBetween A ρ z w).toContinuousLinearMap (D.fiberBetween A ρ z w)
    (D.fiberBetween_period A ρ z w)
  intro v
  exact (congrArg Subtype.val (LinearMap.congr_fun (D.polarizedIso_rational A ρ z w hH) v)).trans
    (D.rationalBetween_coe A ρ z w v)

end

end OAI.RepresentationTheory.Theta.Geometric
