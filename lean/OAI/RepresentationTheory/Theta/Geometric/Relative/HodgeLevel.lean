import OAI.RepresentationTheory.Theta.Geometric.Relative.HodgePointMap
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.BetweenCenter
import OAI.RepresentationTheory.Theta.Geometric.PresentedLevelComparison

/-! # Hodge Level -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The algebraized comparison preserves the original full level on
every test scheme, by its exact action on all native level points. -/

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

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.polarizedIso_level (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (a : LocallyConstant T.left (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Labels.LevelCover.Coefficients g N)) :
    (((A.level.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left).hom.app (.op T)) a).val ≫
      (D.polarizedIso A ρ z w hH).hom =
      (((A.level.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left).hom.app (.op T)) a).val := by
  let : IsMonHom (D.polarizedIso A ρ z w hH).hom := D.polarizedIso_group A ρ z w hH
  apply PresentedLevelComparison.original_level_comparison_of_presented_points
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z))
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w))
    (A.level.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
    (A.level.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left)
    (D.polarizedIso A ρ z w hH).hom ?_ T a
  intro b
  exact (congrFun (D.polarizedIso_native_points A ρ z w hH)
    (Intrinsic.LevelTransport.presentedFullLevelPoint A.level (Intrinsic.FamilyFrames.familyChartParameter C z)
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)) b)).trans
    (D.fiberBetween_level A ρ z w b)

end

end OAI.RepresentationTheory.Theta.Geometric
