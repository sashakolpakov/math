import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RelativeForgetClass
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CycleRelativeAbsolute
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SupportedCycle

/-! # Component Ordinary Image -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ComponentOrdinaryImage

noncomputable section

/-! # The unchanged Paul-Lez component class is the actual absolute cycle image -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace OAI.AlgebraicTopology.Singular
attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p)
local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X
local notation "D" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DimensionCycleSupports.originalDimensionSupport X p x
local notation "S" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x.val
local instance CMOriginalComponentOrdinaryImage.localInstance1 : TopologicalSpace (V).analyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X

theorem originalComponentOrdinaryImage :
    CycleClassMap.originalCycleComponentClass X p x =
    BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X (2 * p)
      (NormalCoclassComparison.normalCoclassCoefficient p • (@SupportedCycle.nativeAbsoluteCycleClass (V) p (D))) := by
  dsimp only [instOfNatAtLeastTwo, Rat.instField]
  unfold CycleClassMap.originalCycleComponentClass ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSheafClass
  rw [SupportedCycle.originalSupportedCycleInverse, RelativeForgetClass.originalRelativeClass_forgetSupport]
  simp only [ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport, SetLike.coe]
  rw [CycleRelativeAbsolute.originalCycleRelativeAbsolute]
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ComponentOrdinaryImage
