import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

/-! # Nested Support Stalk -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupportStalk

noncomputable section

/-! Stalk maps of nested reduced supports compose to the native ThomClass
support map, including all point identifications. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport

theorem stalk_comp {X Y Z : Scheme} (i : Z ⟶ Y) (j : Y ⟶ X) (k : Z ⟶ X)
    (hfac : i ≫ j = k) (z : Z) (y : Y) (x : X)
    (hy : i z = y) (hx : j y = x) (hz : k z = x) :
    eqToHom (congrArg (fun t => X.presheaf.stalk t) hx.symm) ≫ j.stalkMap y ≫
        eqToHom (congrArg (fun t => Y.presheaf.stalk t) hy.symm) ≫ i.stalkMap z =
      eqToHom (congrArg (fun t => X.presheaf.stalk t) hz.symm) ≫ k.stalkMap z := by
  subst y
  subst x
  subst k
  simp only [eqToHom_refl, Category.id_comp, Scheme.Hom.stalkMap_comp]

variable (X : Scheme) (A W : IrreducibleCloseds X) (hAW : A ≤ W)
  (x : X) (hxA : x ∈ (A : Set X)) (hxW : x ∈ (W : Set X))

def stalkMap :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hxW) ⟶
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA) :=
  eqToHom (congrArg (fun t => (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk t)
    (NestedSupport.inclusion_preimage X A W hAW x hxA hxW).symm) ≫
      (NestedSupport.inclusion X A W hAW).stalkMap (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA)

theorem comp : Local.Principal.supportStalkMap X W x hxW ≫ NestedSupportStalk.stalkMap X A W hAW x hxA hxW =
    Local.Principal.supportStalkMap X A x hxA := by
  exact stalk_comp (NestedSupport.inclusion X A W hAW) (CycleClass.Geometric.GenericPoint.reducedSupportι W) (CycleClass.Geometric.GenericPoint.reducedSupportι A)
    (NestedSupport.inclusion_fac X A W hAW) (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA) (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hxW) x
    (NestedSupport.inclusion_preimage X A W hAW x hxA hxW) (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hxW)
    (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec A x hxA)

theorem apply_comp (r : X.presheaf.stalk x) :
    NestedSupportStalk.stalkMap X A W hAW x hxA hxW (Local.Principal.supportStalkMap X W x hxW r) = Local.Principal.supportStalkMap X A x hxA r :=
  congrArg (fun f : X.presheaf.stalk x ⟶
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA) => f r)
      (comp X A W hAW x hxA hxW)

theorem surjective : Function.Surjective (NestedSupportStalk.stalkMap X A W hAW x hxA hxW) := by
  intro t
  obtain ⟨r, hr⟩ := Local.Principal.supportStalkMap_surjective X A x hxA t
  exact ⟨Local.Principal.supportStalkMap X W x hxW r, (apply_comp X A W hAW x hxA hxW r).trans hr⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupportStalk
