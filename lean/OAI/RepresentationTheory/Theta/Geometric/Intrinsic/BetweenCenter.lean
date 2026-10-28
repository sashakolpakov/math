import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.BetweenMaps
import OAI.RepresentationTheory.Theta.Geometric.EquivalenceSquares

/-! # Between Center -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic

noncomputable section

section

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

theorem CompatibleTransport.NativeCompatibleTransport.fiberBetween_apply_center (z w : D.neighborhood)
    (v : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C))).variety.toOver) :
    D.fiberBetween A ρ z w
      (F.nativeFiberTransport z (D.subset_frame z.property) (D.subset_chart z.property)
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)))
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z)) v) =
      F.nativeFiberTransport w (D.subset_frame w.property) (D.subset_chart w.property)
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)))
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C w)) v :=
  EquivalenceSquares.equivalence_between_apply_center
    (F.nativeFiberTransport z (D.subset_frame z.property) (D.subset_chart z.property)
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)))
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z))).toEquiv
    (F.nativeFiberTransport w (D.subset_frame w.property) (D.subset_chart w.property)
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)))
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C w))).toEquiv v

end

/-! The actual real and point transports between two fibers retain
their original rational map and every original full-level label. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped Classical

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation Family.FieldActions.familyFieldPeriodAction Family.PELCoordinates.familyPELCoordinates
  FamilyFrames.NativeFamilyPeriodFrame.nativeRealTransport FamilyFrames.NativeFamilyPeriodFrame.nativeRationalEquiv
  FamilyFrames.NativeFamilyPeriodFrame.nativeFiberTransport
  LevelTransport.presentedFullLevelPoint CompatibleTransport.NativeCompatibleTransport.fiberBetween

variable {E : Type} [Field E] [NumberField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : CompatibleTransport.NativeCompatibleTransport A ρ F)

theorem CompatibleTransport.NativeCompatibleTransport.fiberBetween_level (z w : D.neighborhood) (a : Multiplicative (Fin (2 * g) → ZMod N)) :
    D.fiberBetween A ρ z w
      (LevelTransport.presentedFullLevelPoint A.level (FamilyFrames.familyChartParameter C z)
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z)) a) =
      LevelTransport.presentedFullLevelPoint A.level (FamilyFrames.familyChartParameter C w)
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C w)) a :=
  (congrArg (fun u : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z)).variety.toOver =>
    D.fiberBetween A ρ z w u) (D.level z a).symm).trans
      ((D.fiberBetween_apply_center A ρ z w
        (LevelTransport.presentedFullLevelPoint A.level (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C))
          (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C))) a)).trans (D.level w a))

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic
