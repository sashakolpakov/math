import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.StalkProperties

/-! # Stalk -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Stalk

noncomputable section

/-! The projection map on a reduced support's native stalk, including
the point identifications in ThomClass's local support module. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

variable {X Y : Scheme} (f : X ⟶ Y) (B : IrreducibleCloseds X)
  (x : X) (hx : x ∈ (B : Set X))

def map : Y.presheaf.stalk (f x) ⟶
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage B x hx) :=
  f.stalkMap x ≫ Local.Principal.supportStalkMap X B x hx

theorem comp_congr {Z : Scheme} (i : Z ⟶ X) (z : Z) (h : i z = x) :
    f.stalkMap x ≫ eqToHom (congrArg (fun t => X.presheaf.stalk t) h.symm) ≫ i.stalkMap z =
      eqToHom (congrArg (fun t => Y.presheaf.stalk t) (congrArg f h).symm) ≫ (i ≫ f).stalkMap z := by
  subst x
  simp [Scheme.Hom.stalkMap_comp]

theorem eq_native : map f B x hx =
    eqToHom (congrArg (fun t => Y.presheaf.stalk t)
      (congrArg f (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec B x hx)).symm) ≫
        (CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ f).stalkMap (CycleClass.Thom.IntersectionGeometry.supportPreimage B x hx) :=
  comp_congr f x (CycleClass.Geometric.GenericPoint.reducedSupportι B) (CycleClass.Thom.IntersectionGeometry.supportPreimage B x hx) (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec B x hx)

theorem properties
    (H : ((CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ f).stalkMap (CycleClass.Thom.IntersectionGeometry.supportPreimage B x hx)).hom.Flat ∧
      ((CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ f).stalkMap (CycleClass.Thom.IntersectionGeometry.supportPreimage B x hx)).hom.FormallyUnramified ∧
      ((CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ f).stalkMap (CycleClass.Thom.IntersectionGeometry.supportPreimage B x hx)).hom.EssFiniteType) :
    (map f B x hx).hom.Flat ∧ (map f B x hx).hom.FormallyUnramified ∧
      (map f B x hx).hom.EssFiniteType := by
  rw [eq_native]
  exact ⟨(RingHom.Flat.respectsIso.cancel_left_isIso _ _).mpr H.1,
    (RingHom.FormallyUnramified.respectsIso.cancel_left_isIso _ _).mpr H.2.1,
    (RingHom.EssFiniteType.respectsIso.cancel_left_isIso _ _).mpr H.2.2⟩

theorem of_etale_open (U : (CycleClass.Geometric.GenericPoint.reducedSupportScheme B).Opens)
    [Etale (U.ι ≫ (CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ f))] (hu : CycleClass.Thom.IntersectionGeometry.supportPreimage B x hx ∈ U) :
    (map f B x hx).hom.Flat ∧ (map f B x hx).hom.FormallyUnramified ∧
      (map f B x hx).hom.EssFiniteType :=
  properties f B x hx (ProjectionFormula.Etale.StalkProperties.of_open (CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ f) U _ hu)

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Stalk
