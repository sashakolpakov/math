import OAI.RepresentationTheory.Theta.Geometric.Relative.IntegralPolarization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.HodgeAlgebraization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HodgeInverse

/-! # Polarized Hodge Iso -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Algebraize the constructed integral rational Hodge comparison
between original fibers, retaining its exact polarization and period map. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

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

def Intrinsic.CompatibleTransport.NativeCompatibleTransport.polarizedIso : (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left).scheme ≅
    (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left).scheme :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.HodgeAlgebraization.polarizedHodgeAbelianIso (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
    (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left) (D.rationalBetween A ρ z w) hH
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.HodgeInverse.isHodgeMap_inverse _ _ (D.rationalBetween A ρ z w) hH)
    (fun v => (D.rationalBetween_integral A ρ z w v).symm)

instance Intrinsic.CompatibleTransport.NativeCompatibleTransport.polarizedIso_group : IsMonHom (D.polarizedIso A ρ z w hH).hom :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.HodgeAlgebraization.polarizedHodgeAbelianIso_isMonHom _ _ _ _ _ _

attribute [local irreducible] Intrinsic.CompatibleTransport.NativeCompatibleTransport.polarizedIso

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.polarizedIso_rational :
    let : IsMonHom (D.polarizedIso A ρ z w hH).hom := D.polarizedIso_group A ρ z w hH
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift
      ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left))).hom ≫
        (D.polarizedIso A ρ z w hH).hom ≫
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left)
          (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left))).inv) =
      (D.rationalBetween A ρ z w).toLinearMap := by
  let : IsMonHom (D.polarizedIso A ρ z w hH).hom := D.polarizedIso_group A ρ z w hH
  unfold Intrinsic.CompatibleTransport.NativeCompatibleTransport.polarizedIso
  exact AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.HodgeIso.AbelianIntrinsicAdapter.originalHodgeIso_rational _ _ _ _ _ _ _ _

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.polarizedIso_polarization :
    let : IsMonHom (D.polarizedIso A ρ z w hH).hom := D.polarizedIso_group A ρ z w hH
    (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left).polarization.isogeny.hom ≫
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnderlyingIso.dualFamilyIso (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left).dual
        (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left).dual (D.polarizedIso A ρ z w hH)).hom =
      (D.polarizedIso A ρ z w hH).hom ≫ (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left).polarization.isogeny.hom := by
  let : IsMonHom (D.polarizedIso A ρ z w hH).hom := D.polarizedIso_group A ρ z w hH
  unfold Intrinsic.CompatibleTransport.NativeCompatibleTransport.polarizedIso
  exact AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.HodgeAlgebraization.polarizedHodgeAbelianIso_polarization
    (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left) (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left)
    (D.rationalBetween A ρ z w) hH
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.HodgeInverse.isHodgeMap_inverse _ _ (D.rationalBetween A ρ z w) hH)
    (fun v => (D.rationalBetween_integral A ρ z w v).symm)
    (fun v u => D.rationalBetween_polarization A ρ z w v u)

end

end OAI.RepresentationTheory.Theta.Geometric
