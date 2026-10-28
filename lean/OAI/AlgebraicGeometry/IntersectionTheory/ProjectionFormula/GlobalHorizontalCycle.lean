import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFamilyFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalWeightSupport

/-! # Global Horizontal Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalHorizontalCycle

noncomputable section

/-! A fixed finite collection of global family components gives a
genuine finite weighted endpoint cycle. Vertical components vanish,
and its coefficients are the global parameter-weight sums. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Polynomial Classical

variable (Z : Scheme) [AlgebraicGeometry.IsNoetherian Z] (t : Z ⟶ Spec (.of ℂ[X]))
  (c : IrreducibleCloseds Z → ℚ) (F : Finset (IrreducibleCloseds Z))

def cycle (a : ℂ) : Z →₀ ℚ :=
  ∑ C ∈ F, if hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) then
    c C • HorizontalFamilyFiber.Family.cycle Z C t hη a else 0

theorem apply (a : ℂ) (x : Z) : cycle Z t c F a x =
    ∑ C ∈ F, c C * GlobalParameterSum.Weights.weight Z x (Affine.ParameterFiber.germ ℂ t x a) C := by
  rw [cycle, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro C _
  by_cases hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)
  · rw [dite_eq_left hη, Finsupp.smul_apply, HorizontalFamilyFiber.Family.apply, smul_eq_mul]
  · rw [dite_eq_right hη, Finsupp.zero_apply, GlobalWeightSupport.nonhorizontal Z t C hη x a, mul_zero]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalHorizontalCycle
