import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantDegreeBridge
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SupportedCycle
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CycleRelativeAbsolute
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.EvenHodgeClasses

/-! # Even Cycle Bridge -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.EvenCycleBridge

noncomputable section

section

/-! # The actual absolute cycle class under the original constant-sheaf comparison -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint
attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom]
local instance CMOriginalNativeCycleImage.localInstance1 : TopologicalSpace (BundledAbelianBridge.originalIntegralProjectiveVariety X).analyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X

theorem schemeConstantBridge_congr (n : ℕ)
    (a b : (BundledAbelianBridge.originalIntegralProjectiveVariety X).rationalCohomology n)
    (h : a = b) :
    BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X n a =
      BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X n b := by
  cases h
  rfl

theorem originalNativeCycleImage (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p) :
    BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X (2 * p)
      ((two_mul p).symm ▸ (DimensionCycleSupports.originalDimensionSupport X p x).rationalCycleClass) =
    BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X (2 * p)
      (@SupportedCycle.nativeAbsoluteCycleClass (BundledAbelianBridge.originalIntegralProjectiveVariety X) p
        (DimensionCycleSupports.originalDimensionSupport X p x)) := by
  exact schemeConstantBridge_congr X (2 * p) _ _
    (@SupportedCycle.nativeRationalCycleClass_untransport (BundledAbelianBridge.originalIntegralProjectiveVariety X) p
      (DimensionCycleSupports.originalDimensionSupport X p x))

end

section

/-! # Even-degree transport of the same original Betti comparison -/
open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint
attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

def originalNativeDegreeCast {n m : ℕ} (h : n = m)
    (a : (BundledAbelianBridge.originalIntegralProjectiveVariety X).rationalCohomology n) :
    (BundledAbelianBridge.originalIntegralProjectiveVariety X).rationalCohomology m :=
  @Eq.rec ℕ n (fun k _ => (BundledAbelianBridge.originalIntegralProjectiveVariety X).rationalCohomology k)
    a m h

theorem schemeConstantTransDegreeBridge {n m : ℕ} (h : n = m)
    (a : (BundledAbelianBridge.originalIntegralProjectiveVariety X).rationalCohomology n) :
    ((BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X n).trans
      (EvenHodgeClasses.originalCohomologyDegreeEquiv X h)) a =
    BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X m (originalNativeDegreeCast X h a) := by
  cases h
  rfl

theorem originalEvenBettiBridge_apply (p : ℕ)
    (a : (BundledAbelianBridge.originalIntegralProjectiveVariety X).rationalCohomology (p + p)) :
    EvenHodgeClasses.originalEvenBettiBridge X p a =
      EvenHodgeClasses.originalCohomologyDegreeEquiv X (n := p + p) (m := 2 * p) (two_mul p).symm
        (BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X (p + p) a) := by
  rfl

theorem schemeConstantNativeDegreeBridge {n m : ℕ} (h : n = m)
    (a : (BundledAbelianBridge.originalIntegralProjectiveVariety X).rationalCohomology n) :
    EvenHodgeClasses.originalCohomologyDegreeEquiv X h (BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X n a) =
      BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X m (originalNativeDegreeCast X h a) := by
  cases h
  rfl

theorem originalEvenBridgeTransport (p : ℕ)
    (a : (BundledAbelianBridge.originalIntegralProjectiveVariety X).rationalCohomology (p + p)) :
    EvenHodgeClasses.originalEvenBettiBridge X p a =
      BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X (2 * p)
        (originalNativeDegreeCast X (two_mul p).symm a) := by
  convert (schemeConstantTransDegreeBridge X (n := p + p) (m := 2 * p)
    (two_mul p).symm a) using 2
  rfl

theorem originalEvenNativeCycleImage (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p) :
    BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X (2 * p)
      (originalNativeDegreeCast X (two_mul p).symm
        (DimensionCycleSupports.originalDimensionSupport X p x).rationalCycleClass) =
    BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X (2 * p)
      (@SupportedCycle.nativeAbsoluteCycleClass (BundledAbelianBridge.originalIntegralProjectiveVariety X) p
        (DimensionCycleSupports.originalDimensionSupport X p x)) := by
  apply schemeConstantBridge_congr X (2 * p)
  simpa only [originalNativeDegreeCast] using!
    @SupportedCycle.nativeRationalCycleClass_untransport (BundledAbelianBridge.originalIntegralProjectiveVariety X) p
      (DimensionCycleSupports.originalDimensionSupport X p x)

end

/-! # The original even-degree bridge preserves the actual cycle's absolute class -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular
attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom]
local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X

variable (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p)
local instance CMOriginalEvenCycleBridge.localInstance1 : TopologicalSpace (V).analyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X
local notation "D" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DimensionCycleSupports.originalDimensionSupport X p x

theorem originalEvenCycleBridge :
    EvenHodgeClasses.originalEvenBettiBridge X p (D).rationalCycleClass =
    BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X (2 * p)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ)
        (TopCat.of (V).analyticSpace)
        (Set.range (CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticInclusion (D)))ᶜ
        (2 * p) (D).rationalSupportedCycleClass) := by
  have ht := originalEvenBridgeTransport X p (D).rationalCycleClass
  have hi := originalEvenNativeCycleImage X p x
  dsimp only [instOfNatAtLeastTwo] at ht hi ⊢
  exact ht.trans hi

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.EvenCycleBridge
