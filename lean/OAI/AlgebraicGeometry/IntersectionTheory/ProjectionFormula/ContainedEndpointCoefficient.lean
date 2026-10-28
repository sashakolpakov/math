import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ContainedFamilyCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalEndpointCycleCoefficient

/-! # Contained Endpoint Coefficient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ContainedEndpointCoefficient

noncomputable section

/-! The rationally equivalent contained endpoint cycle has exactly
the fixed global component-weight sum at each native source point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)
  (c : IrreducibleCloseds (Projective.MatrixFamily.Family.space A) → ℚ)
  (F : Finset (IrreducibleCloseds (Projective.MatrixFamily.Family.space A)))
  (hF : ∀ C ∈ F, (C : Set (Projective.MatrixFamily.Family.space A)) ⊆
    Set.range (Projective.FamilyOnSource.Family.toAmbient X A))
  (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)

include hF in
theorem point (x : X.carrier) :
    CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A) (ContainedFamilyCycle.Family.cycle X A c F a) x =
    GlobalHorizontalCycle.cycle (Projective.MatrixFamily.Family.space A)
      (Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A) c F a
        (Projective.MatrixFamily.Family.specialization A a ha (X.embedding x)) := by
  have hi := PushforwardFiber.pointPushforward_uniqueFiber X.embedding x (X.embedding x) rfl
    (fun y hy => X.embedding.isClosedEmbedding.injective hy)
    (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A) (ContainedFamilyCycle.Family.cycle X A c F a))
  rw [Principal.ClosedSectionCycle.residueDegree_immersion, Nat.cast_one, mul_one] at hi
  have he := congrArg (fun z : Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension →₀ ℚ => z (X.embedding x))
    (ContainedFamilyCycle.Family.projection X A c F hF a)
  exact hi.symm.trans (he.trans (GlobalEndpointCycleCoefficient.apply A c F a ha (X.embedding x)))

include hF in
theorem coefficient (p : ℕ) (B : X.DimensionCycleSupport p) :
    CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A)
      (ContainedFamilyCycle.Family.cycle X A c F a)) B =
    ∑ C ∈ F, c C * GlobalParameterSum.Weights.weight (Projective.MatrixFamily.Family.space A)
      (Projective.MatrixFamily.Family.specialization A a ha (X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint B.val)))
      (Affine.ParameterFiber.germ ℂ (Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A)
        (Projective.MatrixFamily.Family.specialization A a ha (X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint B.val))) a) C := by
  rw [Principal.ClosedSectionCycle.degreeComponent_apply, point X A c F hF a ha,
    GlobalHorizontalCycle.apply]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ContainedEndpointCoefficient
