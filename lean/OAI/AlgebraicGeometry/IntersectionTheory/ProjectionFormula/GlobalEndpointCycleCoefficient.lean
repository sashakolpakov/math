import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalHorizontalCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.EndpointFiber

/-! # Global Endpoint Cycle Coefficient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalEndpointCycleCoefficient

noncomputable section

/-! Projecting a global weighted family cycle at a good scalar
retains exactly its coefficient at the marked ambient point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)
  (c : IrreducibleCloseds (Projective.MatrixFamily.Family.space A) → ℚ)
  (F : Finset (IrreducibleCloseds (Projective.MatrixFamily.Family.space A)))
  (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)

theorem supported :
    ((GlobalHorizontalCycle.cycle (Projective.MatrixFamily.Family.space A)
      (Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A) c F a).support :
        Set (Projective.MatrixFamily.Family.space A)) ⊆
      Set.range (Projective.MatrixFamily.Family.specialization A a ha) := by
  intro y hy
  rw [Projective.EndpointFiber.range]
  change Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A y = Affine.ParameterFiber.point ℂ a
  by_contra hn
  apply Finsupp.mem_support_iff.mp hy
  rw [GlobalHorizontalCycle.apply]
  apply Finset.sum_eq_zero
  intro C _
  rw [GlobalWeightSupport.outside_fiber _ _ y a hn C, mul_zero]

theorem apply (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :
    CyclePushforward.pointPushforward (Projective.FamilySupport.Family.projection A)
      (GlobalHorizontalCycle.cycle (Projective.MatrixFamily.Family.space A)
        (Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A) c F a) x =
    GlobalHorizontalCycle.cycle (Projective.MatrixFamily.Family.space A)
      (Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A) c F a
        (Projective.MatrixFamily.Family.specialization A a ha x) := by
  let := Projective.FamilySections.Family.ambient_closed A a ha
  exact Principal.ClosedSectionCycle.apply (Projective.MatrixFamily.Family.specialization A a ha)
    (Projective.FamilySupport.Family.projection A) (Projective.FamilySupport.Family.specialization_projection A a ha)
    _ (supported A c F a ha) x

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalEndpointCycleCoefficient
