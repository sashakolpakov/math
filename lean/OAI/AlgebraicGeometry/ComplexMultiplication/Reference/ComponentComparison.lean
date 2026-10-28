import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ComponentOrdinaryImage
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.EvenCycleBridge

/-! # Component Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ComponentComparison

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # Genuine native component classes equal the unchanged Paul-Lez classes up to one nonzero normalizer -/
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
local instance CMOriginalComponentComparison.localInstance1 : TopologicalSpace (V).analyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X

theorem originalComponentClass_comparison :
    NormalCoclassComparison.normalCoclassCoefficient p • EvenHodgeClasses.originalEvenBettiBridge X p (D).rationalCycleClass =
    CycleClassMap.originalCycleComponentClass X p x := by
  have ho := ComponentOrdinaryImage.originalComponentOrdinaryImage X p x
  have hb := EvenCycleBridge.originalEvenCycleBridge X p x
  have hn : BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X (2 * p)
      (NormalCoclassComparison.normalCoclassCoefficient p • (@SupportedCycle.nativeAbsoluteCycleClass (V) p (D))) =
      NormalCoclassComparison.normalCoclassCoefficient p • EvenHodgeClasses.originalEvenBettiBridge X p (D).rationalCycleClass := by
    rw [map_smul]
    exact congrArg (fun z : H^(2 * p)(X; ℚ) => NormalCoclassComparison.normalCoclassCoefficient p • z) hb.symm
  dsimp only [instOfNatAtLeastTwo] at hn ho ⊢
  exact hn.symm.trans ho.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ComponentComparison
