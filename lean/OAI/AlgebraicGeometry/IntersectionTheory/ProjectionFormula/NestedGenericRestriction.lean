import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction

/-! # Nested Generic Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedGenericRestriction

noncomputable section

/-! Restriction of a rational function that is a unit at the generic
point of a nested support, through the actual closed-immersion stalk map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport

def stalkToField (Y : Scheme) [IsIntegral Y] (y : Y) : Y.presheaf.stalk y ⟶ Y.functionField :=
  CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) Y.functionField)

variable (X : Scheme) (C W : IrreducibleCloseds X) (hCW : C ≤ W)

def point : CycleClass.Geometric.GenericPoint.reducedSupportScheme W := CycleClass.Thom.IntersectionGeometry.supportPreimage W (CycleClass.Thom.IntersectionGeometry.supportPoint C)
  (hCW (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem)

def map : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (point X C W hCW) ⟶
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme C).functionField :=
  eqToHom (congrArg (fun x => (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk x)
    (NestedSupport.inclusion_genericPoint X C W hCW).symm) ≫
      (NestedSupport.inclusion X C W hCW).stalkMap (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) ≫
        stalkToField (CycleClass.Geometric.GenericPoint.reducedSupportScheme C) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C))

theorem section_eq (U : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens)
    [Nonempty ((NestedSupport.inclusion X C W hCW) ⁻¹ᵁ U)]
    (hx : point X C W hCW ∈ U) (a : Γ(CycleClass.Geometric.GenericPoint.reducedSupportScheme W, U)) :
    NestedGenericRestriction.map X C W hCW ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.germ U (point X C W hCW) hx a) =
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme C).germToFunctionField ((NestedSupport.inclusion X C W hCW) ⁻¹ᵁ U)
        ((NestedSupport.inclusion X C W hCW).app U a) := by
  simpa only [NestedGenericRestriction.map, stalkToField, CommRingCat.comp_apply] using
    congrArg (fun f : Γ(CycleClass.Geometric.GenericPoint.reducedSupportScheme W, U) ⟶ (CycleClass.Geometric.GenericPoint.reducedSupportScheme C).functionField => f a)
    (Support.LocalFraction.Restriction.germ_square (NestedSupport.inclusion X C W hCW) U
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) (point X C W hCW)
      (NestedSupport.inclusion_genericPoint X C W hCW) hx)

variable (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)
  (hunit : ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (point X C W hCW),
    IsUnit u ∧ algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField u = g)

def function : (CycleClass.Geometric.GenericPoint.reducedSupportScheme C).functionField := NestedGenericRestriction.map X C W hCW hunit.choose

theorem function_ne_zero : function X C W hCW g hunit ≠ 0 :=
  ((hunit.choose_spec.1).map (NestedGenericRestriction.map X C W hCW).hom).ne_zero

theorem function_eq (u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (point X C W hCW))
    (hu : algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField u = g) :
    function X C W hCW g hunit = NestedGenericRestriction.map X C W hCW u := by
  apply congrArg (NestedGenericRestriction.map X C W hCW)
  exact IsFractionRing.injective _ _ (hunit.choose_spec.2.trans hu.symm)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedGenericRestriction
