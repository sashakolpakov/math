import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CycleRelativeAbsolute
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SupportedCycle
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.EvenHodgeClasses

/-! # Constant Degree Bridge -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantDegreeBridge

noncomputable section

/-! # The original even-degree bridge preserves the actual cycle's absolute class -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular
attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom]
local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X

theorem schemeConstantDegreeBridge {n m : ℕ} (h : n = m)
    (a : (V).rationalCohomology n) :
    EvenHodgeClasses.originalCohomologyDegreeEquiv X h (BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X n a) =
    BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X m (h ▸ a) := by
  cases h
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantDegreeBridge
