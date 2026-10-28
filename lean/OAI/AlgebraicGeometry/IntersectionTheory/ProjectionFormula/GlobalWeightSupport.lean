import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalParameterSum
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterDominance
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterRestriction

/-! # Global Weight Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalWeightSupport

noncomputable section

/-! Parameter weights are supported on their scalar fiber and
vanish on every component whose projective parameter is not dominant. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Polynomial

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalParameterSum.Weights

theorem zero_of_isUnit (Z : Scheme) (x : Z) (r : Z.presheaf.stalk x) (hr : IsUnit r)
    (C : IrreducibleCloseds Z) : GlobalParameterSum.Weights.weight Z x r C = 0 := by
  unfold GlobalParameterSum.Weights.weight
  split_ifs with hx hn
  · rw [Ring.ord_of_isUnit (hr.map (Local.Principal.supportStalkMap Z C x hx).hom)]
    rfl
  · rfl
  · rfl

theorem outside_fiber (Z : Scheme) (t : Z ⟶ Spec (.of ℂ[X])) (x : Z) (a : ℂ)
    (hx : t x ≠ Affine.ParameterFiber.point ℂ a) (C : IrreducibleCloseds Z) :
    GlobalParameterSum.Weights.weight Z x (Affine.ParameterFiber.germ ℂ t x a) C = 0 := by
  apply zero_of_isUnit
  apply IsLocalRing.notMem_maximalIdeal.mp
  exact fun h => hx ((Affine.ParameterFiber.germ_mem_maximalIdeal ℂ t x a).mp h)

theorem nonhorizontal (Z : Scheme) (t : Z ⟶ Spec (.of ℂ[X])) (C : IrreducibleCloseds Z)
    (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) ≠ genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (x : Z) (a : ℂ) : GlobalParameterSum.Weights.weight Z x (Affine.ParameterFiber.germ ℂ t x a) C = 0 := by
  by_cases htx : t x = Affine.ParameterFiber.point ℂ a
  · by_cases hx : x ∈ (C : Set Z)
    · rw [GlobalParameterSum.Weights.weight, dite_eq_left hx]
      by_cases hr : Local.Principal.supportStalkMap Z C x hx (Affine.ParameterFiber.germ ℂ t x a) ≠ 0
      · have hy : (CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) (CycleClass.Thom.IntersectionGeometry.supportPreimage C x hx) = Affine.ParameterFiber.point ℂ a := by
          change t (CycleClass.Geometric.GenericPoint.reducedSupportι C (CycleClass.Thom.IntersectionGeometry.supportPreimage C x hx)) = _
          rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]
          exact htx
        have hg : Affine.ParameterFiber.germ ℂ (CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) (CycleClass.Thom.IntersectionGeometry.supportPreimage C x hx) a ≠ 0 :=
          (Affine.ParameterRestriction.support Z C t x hx a) ▸ hr
        exact (hη (Affine.ParameterDominance.projective_generic
          (CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) (CycleClass.Thom.IntersectionGeometry.supportPreimage C x hx) a hy hg)).elim
      · exact ite_eq_right hr
    · rw [GlobalParameterSum.Weights.weight, dite_eq_right hx]
  · exact outside_fiber Z t x a htx C

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalWeightSupport
