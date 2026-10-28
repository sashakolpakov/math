import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.GenericField

/-! # Generic Field -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.GenericField

noncomputable section

/-! Canonical restriction at a support's generic point, and the exact
generic stalk lift of a function from the target. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction.Restriction OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

theorem generic_algebraMap (Y : Scheme) [IsIntegral Y] :
    letI := stalkFunctionFieldAlgebra Y (genericPoint Y)
    CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (genericPoint Y)) Y.functionField) = 𝟙 Y.functionField := by
  change Y.presheaf.stalkSpecializes (specializes_refl (genericPoint Y)) = 𝟙 _
  exact TopCat.Presheaf.stalkSpecializes_refl _ _

private theorem at_generic_aux (X : Scheme) (W : IrreducibleCloseds X)
    (y : CycleClass.Geometric.GenericPoint.reducedSupportScheme W) (he : CycleClass.Geometric.GenericPoint.reducedSupportι W y = CycleClass.Thom.IntersectionGeometry.supportPoint W)
    (hy : y = genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) :
    (eqToHom (congrArg (fun x => X.presheaf.stalk x) he.symm) ≫ (CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap y) ≫
      CommRingCat.ofHom (algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y) (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) =
    eqToHom (congrArg (fun x => X.presheaf.stalk x) (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W).symm) ≫
      (CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) := by
  subst y
  rw [generic_algebraMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme W), Category.comp_id]

theorem toFunctionField_generic (X : Scheme) (W : IrreducibleCloseds X)
    (hx : CycleClass.Thom.IntersectionGeometry.supportPoint W ∈ (W : Set X)) :
    LocalFraction.Restriction.toFunctionField X W (CycleClass.Thom.IntersectionGeometry.supportPoint W) hx =
      eqToHom (congrArg (fun x => X.presheaf.stalk x) (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W).symm) ≫
        (CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) := by
  have hy : CycleClass.Thom.IntersectionGeometry.supportPreimage W (CycleClass.Thom.IntersectionGeometry.supportPoint W) hx = genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) := by
    apply (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective
    exact (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W _ hx).trans (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W).symm
  exact at_generic_aux X W (CycleClass.Thom.IntersectionGeometry.supportPreimage W (CycleClass.Thom.IntersectionGeometry.supportPoint W) hx) (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W _ hx) hy

theorem generic_transport (Y : Scheme) [IsIntegral Y] (y : Y) (hy : y = genericPoint Y) :
    eqToHom (congrArg (fun z => Y.presheaf.stalk z) hy.symm) ≫
      CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) Y.functionField) = 𝟙 Y.functionField := by
  subst y
  rw [generic_algebraMap Y, eqToHom_refl, Category.id_comp]

theorem stalkCongr_eqToHom (X : Scheme) {x y : X} (h : x = y) :
    (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom =
      eqToHom (congrArg (fun z => X.presheaf.stalk z) h) := by
  subst y
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, eqToHom_refl]

theorem stalkMap_congr {X Y : Scheme} (f : X ⟶ Y) {x y : X} (h : x = y) :
    eqToHom (congrArg (fun z => Y.presheaf.stalk z) (congrArg f h)) ≫ f.stalkMap y =
      f.stalkMap x ≫ eqToHom (congrArg (fun z => X.presheaf.stalk z) h) := by
  subst y
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

def germMap {X Y : Scheme} [IsIntegral Y] (f : X ⟶ Y) (x : X) (hx : f x = genericPoint Y) :
    Y.functionField ⟶ X.presheaf.stalk x :=
  eqToHom (congrArg (fun z => Y.presheaf.stalk z) hx.symm) ≫ f.stalkMap x

theorem germMap_congr {X Y : Scheme} [IsIntegral Y] (f : X ⟶ Y) {x y : X} (h : x = y)
    (hx : f x = genericPoint Y) (hy : f y = genericPoint Y) :
    germMap f x hx ≫ eqToHom (congrArg (fun z => X.presheaf.stalk z) h) = germMap f y hy := by
  subst y
  rw [eqToHom_refl, Category.comp_id]

theorem germMap_field {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (hη : f (genericPoint X) = genericPoint Y) (x : X) (hx : f x = genericPoint Y) (g : Y.functionField) :
    algebraMap (X.presheaf.stalk x) X.functionField (germMap f x hx g) = Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g := by
  have h := Divisor.DivisorRestriction.genericFieldMap_stalk f hη x
    (eqToHom (congrArg (fun z => Y.presheaf.stalk z) hx.symm) g)
  have he := congrArg (fun k : Y.functionField ⟶ Y.functionField => k g) (generic_transport Y (f x) hx)
  change algebraMap (Y.presheaf.stalk (f x)) Y.functionField
    (eqToHom (congrArg (fun z => Y.presheaf.stalk z) hx.symm) g) = g at he
  rw [he] at h
  exact h.symm

theorem germMap_restrict {X Y : Scheme} [IsIntegral Y] (f : X ⟶ Y)
    (W : IrreducibleCloseds X) (hx : CycleClass.Thom.IntersectionGeometry.supportPoint W ∈ (W : Set X))
    (hW : f (CycleClass.Thom.IntersectionGeometry.supportPoint W) = genericPoint Y)
    (hη : (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ f) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) = genericPoint Y) :
    germMap f (CycleClass.Thom.IntersectionGeometry.supportPoint W) hW ≫ LocalFraction.Restriction.toFunctionField X W (CycleClass.Thom.IntersectionGeometry.supportPoint W) hx =
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ f) hη := by
  rw [toFunctionField_generic]
  have hw : CycleClass.Thom.IntersectionGeometry.supportPoint W = CycleClass.Geometric.GenericPoint.reducedSupportι W (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) :=
    (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W).symm
  have ht := germMap_congr f hw hW hη
  have hr : Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ f) hη =
      germMap f (CycleClass.Geometric.GenericPoint.reducedSupportι W (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))) hη ≫
        (CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) := by
    rw [Cycles.Functoriality.FunctionFields.Construction.genericFieldMap, Scheme.Hom.stalkMap_comp]
    have he := stalkCongr_eqToHom Y hη.symm
    exact congrArg (fun k : Y.functionField ⟶ Y.presheaf.stalk
      ((CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ f) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))) =>
        k ≫ f.stalkMap (CycleClass.Geometric.GenericPoint.reducedSupportι W (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))) ≫
          (CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))) he
  rw [hr, ← Category.assoc]
  exact congrArg (fun k => k ≫ (CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))) ht

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.GenericField
