import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EmbeddedDivisorDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointPushforwardSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalWeightSupport

/-! # Horizontal Fiber Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFiberDimension

noncomputable section

/-! Every nonzero horizontal fiber coefficient lies on its scalar
fiber and has point-closure dimension one below its global component. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Polynomial

variable (Z : Scheme) [AlgebraicGeometry.IsNoetherian Z] (C : IrreducibleCloseds Z)
  (t : Z ⟶ Spec (.of ℂ[X]))
  (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
    (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))

theorem parameter (a : ℂ) (x : Z) (hx : HorizontalFamilyFiber.Family.cycle Z C t hη a x ≠ 0) :
    t x = Affine.ParameterFiber.point ℂ a := by
  rw [HorizontalFamilyFiber.Family.apply] at hx
  by_contra hn
  exact hx (GlobalWeightSupport.outside_fiber Z t x a hn C)

theorem dimension (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (a : ℂ) (x : Z) (hx : HorizontalFamilyFiber.Family.cycle Z C t hη a x ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + 1 =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C f := by
  let s := (CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) ≫ Projective.FamilyIs.MatrixParameterOpen.affine
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (s ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  change CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι C)
    (Projective.ParameterCycle.cycle s hη a) x ≠ 0 at hx
  obtain ⟨y, hy, he⟩ := PointPushforwardSupport.exists_point (CycleClass.Geometric.GenericPoint.reducedSupportι C) _ x hx
  have hd := EmbeddedDivisorDimension.positive Z f C
    (Projective.LineParameter.pullback s hη - algebraMap ℂ (CycleClass.Geometric.GenericPoint.reducedSupportScheme C).functionField a) y hy
  rwa [he] at hd

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFiberDimension
