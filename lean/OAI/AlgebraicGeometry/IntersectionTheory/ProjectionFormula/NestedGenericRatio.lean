import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedGenericRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupportStalk
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.GenericField

/-! # Nested Generic Ratio -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedGenericRatio

noncomputable section

section

/-! Restricting a generically invertible rational function to a
nested support respects genuine local fractions and ambient germs. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedGenericRestriction OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

variable (X : Scheme) (C W : IrreducibleCloseds X) (hCW : C ≤ W)

theorem comp (hxC : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (C : Set X))
    (hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (W : Set X)) :
    Local.Principal.supportStalkMap X W (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxW ≫ NestedGenericRestriction.map X C W hCW =
      Support.LocalFraction.Restriction.toFunctionField X C (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxC := by
  have h := NestedSupportStalk.stalk_comp (NestedSupport.inclusion X C W hCW) (CycleClass.Geometric.GenericPoint.reducedSupportι W) (CycleClass.Geometric.GenericPoint.reducedSupportι C)
    (NestedSupport.inclusion_fac X C W hCW) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) (NestedGenericRestriction.point X C W hCW) (CycleClass.Thom.IntersectionGeometry.supportPoint C)
    (NestedSupport.inclusion_genericPoint X C W hCW) (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W _ hxW) (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq C)
  change Local.Principal.supportStalkMap X W (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxW ≫
    (eqToHom (congrArg (fun y => (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y)
      (NestedSupport.inclusion_genericPoint X C W hCW).symm) ≫ (NestedSupport.inclusion X C W hCW).stalkMap (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C))) =
    eqToHom (congrArg (fun y => X.presheaf.stalk y) (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq C).symm) ≫
      (CycleClass.Geometric.GenericPoint.reducedSupportι C).stalkMap (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) at h
  rw [NestedGenericRestriction.map, ← Category.assoc, ← Category.assoc, Category.assoc
    (Local.Principal.supportStalkMap X W (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxW), h]
  rw [NestedGenericRestriction.stalkToField, Support.GenericField.generic_algebraMap, Category.comp_id,
    Support.GenericField.toFunctionField_generic]

theorem ratio (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (hunit : ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (NestedGenericRestriction.point X C W hCW),
      IsUnit u ∧ algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField u = g)
    (a b : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (NestedGenericRestriction.point X C W hCW)) (hb : IsUnit b)
    (hg : g = algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField a /
      algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField b) :
    NestedGenericRestriction.function X C W hCW g hunit =
      NestedGenericRestriction.map X C W hCW a / NestedGenericRestriction.map X C W hCW b := by
  apply (eq_div_iff (hb.map (NestedGenericRestriction.map X C W hCW).hom).ne_zero).mpr
  change NestedGenericRestriction.map X C W hCW hunit.choose *
    NestedGenericRestriction.map X C W hCW b = NestedGenericRestriction.map X C W hCW a
  rw [← map_mul]
  apply congrArg (NestedGenericRestriction.map X C W hCW)
  apply IsFractionRing.injective _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField
  rw [map_mul, hunit.choose_spec.2]
  exact (eq_div_iff (hb.map (algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)).ne_zero).mp hg

theorem ambient_ratio (hxC : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (C : Set X)) (hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (W : Set X))
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (hunit : ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (NestedGenericRestriction.point X C W hCW),
      IsUnit u ∧ algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField u = g)
    (a b : X.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C)) (hb : IsUnit (Local.Principal.supportStalkMap X W (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxW b))
    (hg : g = Support.LocalFraction.Restriction.toFunctionField X W (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxW a /
      Support.LocalFraction.Restriction.toFunctionField X W (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxW b) :
    NestedGenericRestriction.function X C W hCW g hunit =
      Support.LocalFraction.Restriction.toFunctionField X C (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxC a /
        Support.LocalFraction.Restriction.toFunctionField X C (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxC b := by
  have ha := congrArg (fun f : X.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C) ⟶ (CycleClass.Geometric.GenericPoint.reducedSupportScheme C).functionField => f a)
    (comp X C W hCW hxC hxW)
  have hb' := congrArg (fun f : X.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C) ⟶ (CycleClass.Geometric.GenericPoint.reducedSupportScheme C).functionField => f b)
    (comp X C W hCW hxC hxW)
  exact (ratio X C W hCW g hunit (Local.Principal.supportStalkMap X W (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxW a)
    (Local.Principal.supportStalkMap X W (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxW b) hb hg).trans
      (congrArg₂ (fun a b => a / b) ha hb')

end

/-! A fraction of ambient sections which are units at a generic
intersection point gives the same restricted rational function at
every point of that support in the section domain. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Section

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction.Restriction OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedGenericRestriction

theorem ratio (X : Scheme) (C W : IrreducibleCloseds X) (hCW : C ≤ W)
    (hxC : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (C : Set X)) (hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (W : Set X))
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (hunit : ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (NestedGenericRestriction.point X C W hCW),
      IsUnit u ∧ algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField u = g)
    (U : X.Opens) (hU : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ U) (a b : Γ(X, U))
    (ha : IsUnit (X.presheaf.germ U (CycleClass.Thom.IntersectionGeometry.supportPoint C) hU a))
    (hb : IsUnit (X.presheaf.germ U (CycleClass.Thom.IntersectionGeometry.supportPoint C) hU b))
    (hg : g = Support.LocalFraction.Restriction.toFunctionField X W (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxW (X.presheaf.germ U (CycleClass.Thom.IntersectionGeometry.supportPoint C) hU a) /
      Support.LocalFraction.Restriction.toFunctionField X W (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxW (X.presheaf.germ U (CycleClass.Thom.IntersectionGeometry.supportPoint C) hU b))
    (x : X) (hx : x ∈ (C : Set X)) (hxU : x ∈ U) :
    Support.LocalFraction.Restriction.toFunctionField X C x hx (X.presheaf.germ U x hxU a) ≠ 0 ∧
    Support.LocalFraction.Restriction.toFunctionField X C x hx (X.presheaf.germ U x hxU b) ≠ 0 ∧
    NestedGenericRestriction.function X C W hCW g hunit =
      Support.LocalFraction.Restriction.toFunctionField X C x hx (X.presheaf.germ U x hxU a) /
        Support.LocalFraction.Restriction.toFunctionField X C x hx (X.presheaf.germ U x hxU b) := by
  have ha' := (ha.map (Support.LocalFraction.Restriction.toFunctionField X C (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxC).hom).ne_zero
  have hb' := (hb.map (Support.LocalFraction.Restriction.toFunctionField X C (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxC).hom).ne_zero
  have hr := ambient_ratio X C W hCW hxC hxW g hunit
    (X.presheaf.germ U (CycleClass.Thom.IntersectionGeometry.supportPoint C) hU a) (X.presheaf.germ U (CycleClass.Thom.IntersectionGeometry.supportPoint C) hU b)
    (hb.map (Local.Principal.supportStalkMap X W (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxW).hom) hg
  rw [Support.LocalFraction.Restriction.germ_independent X C U (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxC hU x hx hxU a] at ha' hr
  rw [Support.LocalFraction.Restriction.germ_independent X C U (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxC hU x hx hxU b] at hb' hr
  exact ⟨ha', hb', hr⟩

end Section

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedGenericRatio
