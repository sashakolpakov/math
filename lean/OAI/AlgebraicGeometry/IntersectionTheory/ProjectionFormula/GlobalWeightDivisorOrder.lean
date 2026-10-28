import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EveryStalkOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalParameterSum
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterComparison
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterRestriction

/-! # Global Weight Divisor Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalWeightDivisorOrder

noncomputable section

/-! Global support weights are exactly the native geometric
divisor orders of the actual rational parameter on each horizontal
family component. The equality includes every scheme point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Polynomial

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalParameterSum.Weights

theorem nonneg (Z : Scheme) (x : Z) (r : Z.presheaf.stalk x) (C : IrreducibleCloseds Z) :
    0 ≤ GlobalParameterSum.Weights.weight Z x r C := by
  unfold GlobalParameterSum.Weights.weight
  split_ifs <;> positivity

theorem order (Z : Scheme) [IsLocallyNoetherian Z] (x : Z) (r : Z.presheaf.stalk x)
    (C : IrreducibleCloseds Z) (hx : x ∈ (C : Set Z)) :
    GlobalParameterSum.Weights.weight Z x r C =
      ((CycleClass.Geometric.GenericPoint.reducedSupportScheme C).ord
        (algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme C).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage C x hx))
          (CycleClass.Geometric.GenericPoint.reducedSupportScheme C).functionField (Local.Principal.supportStalkMap Z C x hx r))
        (CycleClass.Thom.IntersectionGeometry.supportPreimage C x hx) : ℚ) := by
  rw [GlobalParameterSum.Weights.weight, dite_eq_left hx]
  by_cases hr : Local.Principal.supportStalkMap Z C x hx r ≠ 0
  · rw [ite_eq_left hr]
    exact (congrArg (fun q : ℤ => (q : ℚ))
      (EveryStalkOrder.order (CycleClass.Geometric.GenericPoint.reducedSupportScheme C) (CycleClass.Thom.IntersectionGeometry.supportPreimage C x hx)
        (Local.Principal.supportStalkMap Z C x hx r) hr)).symm
  · rw [ite_eq_right hr, not_ne_iff.mp hr, map_zero, Scheme.ord_zero]
    rfl

theorem parameter (Z : Scheme) [IsLocallyNoetherian Z] (C : IrreducibleCloseds Z)
    (t : Z ⟶ Spec (.of ℂ[X]))
    (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (x : Z) (hx : x ∈ (C : Set Z)) (a : ℂ) :
    let s := (CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) ≫ Projective.FamilyIs.MatrixParameterOpen.affine
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (s ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    GlobalParameterSum.Weights.weight Z x (Affine.ParameterFiber.germ ℂ t x a) C =
      ((CycleClass.Geometric.GenericPoint.reducedSupportScheme C).ord
        (Projective.LineParameter.pullback s hη - algebraMap ℂ (CycleClass.Geometric.GenericPoint.reducedSupportScheme C).functionField a)
        (CycleClass.Thom.IntersectionGeometry.supportPreimage C x hx) : ℚ) := by
  let s := (CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) ≫ Projective.FamilyIs.MatrixParameterOpen.affine
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (s ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  have he := congrArg
    (algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme C).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage C x hx))
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme C).functionField)
    (Affine.ParameterRestriction.support Z C t x hx a)
  have hf := Affine.ParameterComparison.field (CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) hη (CycleClass.Thom.IntersectionGeometry.supportPreimage C x hx) a
  exact (order Z x (Affine.ParameterFiber.germ ℂ t x a) C hx).trans
    (congrArg (fun g => ((CycleClass.Geometric.GenericPoint.reducedSupportScheme C).ord g (CycleClass.Thom.IntersectionGeometry.supportPreimage C x hx) : ℚ)) (he.trans hf))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalWeightDivisorOrder
