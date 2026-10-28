import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalWeightDivisorOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle

/-! # Horizontal Family Fiber -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFamilyFiber

/-! On a horizontal integral family support, the global parameter
weights are a genuine finite cycle: the embedded positive part of the
native principal divisor of the rational parameter. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Polynomial

namespace Family

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalParameterSum.Weights OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm

variable (Z : Scheme) [AlgebraicGeometry.IsNoetherian Z] (C : IrreducibleCloseds Z)
  (t : Z ⟶ Spec (.of ℂ[X]))
  (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
    (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))

def cycle (a : ℂ) : Z →₀ ℚ :=
  let s := (CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) ≫ Projective.FamilyIs.MatrixParameterOpen.affine
  letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (s ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι C)
    (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)
      (Projective.LineParameter.pullback s hη - algebraMap ℂ (CycleClass.Geometric.GenericPoint.reducedSupportScheme C).functionField a)))

theorem apply (a : ℂ) (x : Z) : cycle Z C t hη a x =
    GlobalParameterSum.Weights.weight Z x (Affine.ParameterFiber.germ ℂ t x a) C := by
  let s := (CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) ≫ Projective.FamilyIs.MatrixParameterOpen.affine
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (s ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  by_cases hx : x ∈ (C : Set Z)
  · let y := CycleClass.Thom.IntersectionGeometry.supportPreimage C x hx
    have hy : CycleClass.Geometric.GenericPoint.reducedSupportι C y = x := CycleClass.Thom.IntersectionGeometry.supportPreimage_spec C x hx
    have hu : ∀ z, CycleClass.Geometric.GenericPoint.reducedSupportι C z = x → z = y :=
      fun z hz => (CycleClass.Geometric.GenericPoint.reducedSupportι C).isClosedEmbedding.injective (hz.trans hy.symm)
    rw [cycle, PushforwardFiber.pointPushforward_uniqueFiber (CycleClass.Geometric.GenericPoint.reducedSupportι C) y x hy hu,
      Principal.ClosedSectionCycle.residueDegree_immersion, Nat.cast_one, mul_one,
      PositiveCycle.positivePart_apply, Affine.DivisorNorm.rationalPrincipalDivisor_apply,
      ← GlobalWeightDivisorOrder.parameter Z C t hη x hx a]
    exact max_eq_left (GlobalWeightDivisorOrder.nonneg Z x (Affine.ParameterFiber.germ ℂ t x a) C)
  · have hout : ∀ z : CycleClass.Geometric.GenericPoint.reducedSupportScheme C, CycleClass.Geometric.GenericPoint.reducedSupportι C z ≠ x := by
      intro z hz
      apply hx
      rw [← hz, ← CycleClass.Geometric.GenericPoint.range_reducedSupportι]
      exact ⟨z, rfl⟩
    rw [cycle, PushforwardFiber.pointPushforward_apply_eq_zero (CycleClass.Geometric.GenericPoint.reducedSupportι C) _ x
      (fun z _ => hout z), GlobalParameterSum.Weights.weight, dite_eq_right hx]

end Family

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFamilyFiber

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFamilyFiber.ParameterChange

/-! Equal native affine parameter maps define equal horizontal fiber cycles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Polynomial

theorem cycle {Z : Scheme} [AlgebraicGeometry.IsNoetherian Z] (C : IrreducibleCloseds Z)
    {s t : Z ⟶ Spec (.of ℂ[X])} (h : s = t)
    (hs : ((CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ s) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (ht : ((CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)) (a : ℂ) :
    Family.cycle Z C s hs a = Family.cycle Z C t ht a := by
  subst t
  rfl

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFamilyFiber.ParameterChange

end

end OAI
