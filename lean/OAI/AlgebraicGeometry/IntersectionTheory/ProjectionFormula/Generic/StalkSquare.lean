import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.GenericField

/-! # Stalk Square -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.StalkSquare

noncomputable section

/-! Generic field restriction commutes with the actual stalk maps in
a commutative square of schemes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem stalkMap_congr {X Y : Scheme} {u v : X ⟶ Y} (h : u = v) (x : X) :
    eqToHom (congrArg (fun y => Y.presheaf.stalk y) (congrArg (fun f : X ⟶ Y => f x) h).symm) ≫
      u.stalkMap x = v.stalkMap x := by
  subst v
  simp only [eqToHom_refl, Category.id_comp]

theorem square {S T X Y : Scheme} [IsIntegral S] [IsIntegral T]
    (i : S ⟶ X) (j : T ⟶ Y) (f : X ⟶ Y) (h : S ⟶ T)
    (he : h ≫ j = i ≫ f) (hη : h (genericPoint S) = genericPoint T) :
    let hp : j (genericPoint T) = f (i (genericPoint S)) :=
      (congrArg j hη.symm).trans (congrArg (fun r : S ⟶ Y => r (genericPoint S)) he)
    eqToHom (congrArg (fun y => Y.presheaf.stalk y) hp.symm) ≫
      j.stalkMap (genericPoint T) ≫ Cycles.Functoriality.FunctionFields.Construction.genericFieldMap h hη =
        f.stalkMap (i (genericPoint S)) ≫ i.stalkMap (genericPoint S) := by
  dsimp only
  rw [Cycles.Functoriality.FunctionFields.Construction.genericFieldMap, Support.GenericField.stalkCongr_eqToHom T hη.symm]
  rw [← Category.assoc (j.stalkMap (genericPoint T))]
  rw [← Support.GenericField.stalkMap_congr j hη.symm]
  rw [Category.assoc, ← Scheme.Hom.stalkMap_comp]
  rw [← Category.assoc, eqToHom_trans]
  exact (stalkMap_congr he (genericPoint S)).trans (Scheme.Hom.stalkMap_comp i f (genericPoint S))

theorem at_source_point {S T X Y : Scheme} [IsIntegral S] [IsIntegral T]
    (i : S ⟶ X) (j : T ⟶ Y) (f : X ⟶ Y) (h : S ⟶ T)
    (he : h ≫ j = i ≫ f) (hη : h (genericPoint S) = genericPoint T)
    (x : X) (hx : i (genericPoint S) = x) (hp : j (genericPoint T) = f x) :
    eqToHom (congrArg (fun y => Y.presheaf.stalk y) hp.symm) ≫
      j.stalkMap (genericPoint T) ≫ Cycles.Functoriality.FunctionFields.Construction.genericFieldMap h hη =
        f.stalkMap x ≫ eqToHom (congrArg (fun z => X.presheaf.stalk z) hx.symm) ≫
          i.stalkMap (genericPoint S) := by
  subst x
  simpa only [eqToHom_refl, Category.id_comp] using square i j f h he hη

theorem support {T X Y : Scheme} [IsIntegral T]
    (W : TopologicalSpace.IrreducibleCloseds X) (j : T ⟶ Y) (f : X ⟶ Y)
    (h : CycleClass.Geometric.GenericPoint.reducedSupportScheme W ⟶ T)
    (he : h ≫ j = CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ f)
    (hη : h (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) = genericPoint T)
    (hx : CycleClass.Thom.IntersectionGeometry.supportPoint W ∈ (W : Set X)) (hp : j (genericPoint T) = f (CycleClass.Thom.IntersectionGeometry.supportPoint W)) :
    eqToHom (congrArg (fun y => Y.presheaf.stalk y) hp.symm) ≫
      j.stalkMap (genericPoint T) ≫ Cycles.Functoriality.FunctionFields.Construction.genericFieldMap h hη =
        f.stalkMap (CycleClass.Thom.IntersectionGeometry.supportPoint W) ≫ Support.LocalFraction.Restriction.toFunctionField X W (CycleClass.Thom.IntersectionGeometry.supportPoint W) hx := by
  rw [Support.GenericField.toFunctionField_generic]
  exact at_source_point (CycleClass.Geometric.GenericPoint.reducedSupportι W) j f h he hη (CycleClass.Thom.IntersectionGeometry.supportPoint W)
    (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W) hp

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.StalkSquare
