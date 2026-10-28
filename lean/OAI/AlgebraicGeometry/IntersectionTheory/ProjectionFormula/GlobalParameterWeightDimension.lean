import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalParameterSum
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! # Global Parameter Weight Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalParameterWeightDimension

noncomputable section

/-! A native principal weight vanishes at a support's generic point.
Thus only supports of strictly smaller codimension can contribute at
a prescribed coefficient point on a smooth presentation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

theorem generic_unit (Y : Scheme) [IsIntegral Y] (y : Y) (hy : y = genericPoint Y)
    (r : Y.presheaf.stalk y) (hr : r ≠ 0) : IsUnit r := by
  subst y
  exact isUnit_iff_ne_zero.mpr hr

theorem generic (X : Scheme) (C : IrreducibleCloseds X)
    (r : X.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C)) :
    GlobalParameterSum.Weights.weight X (CycleClass.Thom.IntersectionGeometry.supportPoint C) r C = 0 := by
  classical
  have hx : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (C : Set X) := (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem
  have hy : CycleClass.Thom.IntersectionGeometry.supportPreimage C (CycleClass.Thom.IntersectionGeometry.supportPoint C) hx = genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C) := by
    apply (CycleClass.Geometric.GenericPoint.reducedSupportι C).isClosedEmbedding.injective
    exact (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec C _ hx).trans (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq C).symm
  rw [GlobalParameterSum.Weights.weight, dite_eq_left hx]
  split_ifs with hr
  · rw [Ring.ord_of_isUnit (generic_unit (CycleClass.Geometric.GenericPoint.reducedSupportScheme C) _ hy _ hr)]
    rfl
  · rfl

theorem vanishes (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (C D : IrreducibleCloseds X.carrier) (hcodim : X.supportCodimension C ≤ X.supportCodimension D)
    (r : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C)) :
    GlobalParameterSum.Weights.weight X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C) r D = 0 := by
  classical
  by_cases hx : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (D : Set X.carrier)
  · have hCD : C ≤ D :=
      (Supports.supportPoint_mem_iff_subset
        (X := X.carrier) ⟨(D : Set X.carrier), D.isClosed⟩ C).mp hx
    have he : C = D := by
      by_contra hne
      exact (not_lt_of_ge hcodim) (Supports.codimension_strictAnti X m
        (lt_of_le_of_ne hCD hne))
    subst D
    exact generic X.carrier C r
  · exact dite_eq_right hx

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalParameterWeightDimension
