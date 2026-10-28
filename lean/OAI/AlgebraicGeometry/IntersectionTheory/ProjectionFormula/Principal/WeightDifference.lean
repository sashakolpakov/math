import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalWeightDivisorOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicDivisorRatio

/-! # Weight Difference -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.WeightDifference

noncomputable section

/-! The difference of two native regular-germ divisor weights is
the divisor order of their nonzero rational-function ratio. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction.Restriction

theorem order (X : Scheme) [AlgebraicGeometry.IsNoetherian X]
    (W : IrreducibleCloseds X) (x : X) (hx : x ∈ (W : Set X))
    (a b : X.presheaf.stalk x)
    (ha : Support.LocalFraction.Restriction.toFunctionField X W x hx a ≠ 0) (hb : Support.LocalFraction.Restriction.toFunctionField X W x hx b ≠ 0)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (hg : g = Support.LocalFraction.Restriction.toFunctionField X W x hx a / Support.LocalFraction.Restriction.toFunctionField X W x hx b) :
    GlobalParameterSum.Weights.weight X x a W - GlobalParameterSum.Weights.weight X x b W =
      ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).ord g (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx) : ℚ) := by
  rw [GlobalWeightDivisorOrder.order X x a W hx,
    GlobalWeightDivisorOrder.order X x b W hx, hg,
    IntrinsicDivisorRatio.Intrinsic.ord_div (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) _ _ ha hb, Int.cast_sub]
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.WeightDifference
