import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.SupportCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedCycleRelation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction

/-! # Restricted Support Relation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RestrictedSupportRelation

noncomputable section

/-! Restrict a support rational function to the actual components of
its divisor intersection. Their weighted principal divisors construct a
native ambient rational-equivalence relation. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction.Restriction OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m r : ℕ)
  [SmoothOfRelativeDimension m X.structureMap]
  (D : X.DimensionCycleSupport 1) (W : X.DimensionCycleSupport r) (hDW : ¬ W.val ≤ D.val)
  (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField)
  (hunit : ∀ y : CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val, Order.coheight y = 1 →
    CycleClass.Geometric.GenericPoint.reducedSupportι W.val y ∈ (D.val : Set X.carrier) →
      ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y, IsUnit u ∧
        algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y)
          (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField u = g)
  (A : X.DimensionCycleSupport (1 + r)) (hA : A ∈ (Divisor.SupportCycle.cycle X m r D W).support)

def inner : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val) :=
  NestedSupport.innerSupport X.carrier A.val W.val (Divisor.SupportCycle.support_subset X m r D W hDW A hA).2

theorem inner_height : Order.coheight (CycleClass.Thom.IntersectionGeometry.supportPoint (inner X m r D W hDW A hA)) = 1 :=
  Divisor.SupportCycle.inner_coheight X m r D W hDW A hA

theorem inner_point_mem : CycleClass.Geometric.GenericPoint.reducedSupportι W.val (CycleClass.Thom.IntersectionGeometry.supportPoint (inner X m r D W hDW A hA)) ∈
    (D.val : Set X.carrier) := by
  rw [inner, NestedSupport.innerSupport_point, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]
  exact (Divisor.SupportCycle.support_subset X m r D W hDW A hA).1
    (A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).mem

def unit : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint (inner X m r D W hDW A hA)) :=
  (hunit _ (inner_height X m r D W hDW A hA) (inner_point_mem X m r D W hDW A hA)).choose

theorem unit_isUnit : IsUnit (unit X m r D W hDW g hunit A hA) :=
  (hunit _ (inner_height X m r D W hDW A hA) (inner_point_mem X m r D W hDW A hA)).choose_spec.1

theorem unit_function : algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk
      (CycleClass.Thom.IntersectionGeometry.supportPoint (inner X m r D W hDW A hA))) (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField
      (unit X m r D W hDW g hunit A hA) = g :=
  (hunit _ (inner_height X m r D W hDW A hA) (inner_point_mem X m r D W hDW A hA)).choose_spec.2

def function : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (inner X m r D W hDW A hA)).functionField :=
  Support.LocalFraction.Restriction.toFunctionField (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val) (inner X m r D W hDW A hA)
    (CycleClass.Thom.IntersectionGeometry.supportPoint (inner X m r D W hDW A hA))
    ((inner X m r D W hDW A hA).isIrreducible.isGenericPoint_genericPoint
      (inner X m r D W hDW A hA).isClosed).mem
    (unit X m r D W hDW g hunit A hA)

theorem function_ne_zero : function X m r D W hDW g hunit A hA ≠ 0 :=
  ((unit_isUnit X m r D W hDW g hunit A hA).map (Support.LocalFraction.Restriction.toFunctionField (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val)
    (inner X m r D W hDW A hA) (CycleClass.Thom.IntersectionGeometry.supportPoint (inner X m r D W hDW A hA))
    ((inner X m r D W hDW A hA).isIrreducible.isGenericPoint_genericPoint
      (inner X m r D W hDW A hA).isClosed).mem).hom).ne_zero

def term : X.RationalDimensionCycle (1 + (r + 1)) := NestedCycleRelation.Principal.cycle X (1 + (r + 1)) W.val
  (inner X m r D W hDW A hA) (function X m r D W hDW g hunit A hA)

theorem term_isPrincipal : CycleClass.Thom.IntersectionGeometry.IsPrincipalDivisor X (1 + (r + 1)) (term X m r D W hDW g hunit A hA) :=
  NestedCycleRelation.isPrincipal X m r (1 + (r + 1)) W (inner X m r D W hDW A hA)
    (inner_height X m r D W hDW A hA) (by omega) (function X m r D W hDW g hunit A hA)
    (function_ne_zero X m r D W hDW g hunit A hA)

omit A hA in
def cycle : X.RationalDimensionCycle (1 + (r + 1)) :=
  ∑ A : (Divisor.SupportCycle.cycle X m r D W).support,
    (Divisor.SupportCycle.cycle X m r D W A.val) • term X m r D W hDW g hunit A.val A.property

omit A hA in
theorem cycle_mem : cycle X m r D W hDW g hunit ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (1 + (r + 1)) := by
  apply Submodule.sum_mem
  intro A _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (term_isPrincipal X m r D W hDW g hunit A.val A.property))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RestrictedSupportRelation
