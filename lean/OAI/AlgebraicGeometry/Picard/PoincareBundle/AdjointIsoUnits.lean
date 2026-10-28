import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Adjoint Iso Units -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointIsoUnits

noncomputable section

/-!
# Units and transposed maps under isomorphic adjunctions
-/

open _root_.CategoryTheory

variable {C D : Type*} [Category C] [Category D]
  {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R')
  (α : L ≅ L') (β : R ≅ R') (h : conjugateEquiv a b α.inv = β.hom)

include h in
/-- The units of isomorphic adjunctions are related by their actual mate comparisons. -/
theorem unit_transport (X : C) :
    a.unit.app X ≫ β.hom.app (L.obj X) ≫ R'.map (α.hom.app X) = b.unit.app X := by
  have hu := unit_conjugateEquiv a b α.inv X
  rw [h] at hu
  have hm : R'.map (α.inv.app X) ≫ R'.map (α.hom.app X) = 𝟙 _ := by
    rw [← R'.map_comp, Iso.inv_hom_id_app, R'.map_id]
  calc
    _ = (a.unit.app X ≫ β.hom.app (L.obj X)) ≫ R'.map (α.hom.app X) :=
      (Category.assoc _ _ _).symm
    _ = (b.unit.app X ≫ R'.map (α.inv.app X)) ≫ R'.map (α.hom.app X) :=
      congrArg (fun z => z ≫ R'.map (α.hom.app X)) hu
    _ = _ := by
      rw [Category.assoc, hm]
      exact Category.comp_id _

include h in
/-- Adjunction transposition retains a map after the prescribed left and right comparisons. -/
theorem homEquiv_transport {X : C} {Y : D} (t : L.obj X ⟶ Y) :
    b.homEquiv X Y (α.inv.app X ≫ t) = a.homEquiv X Y t ≫ β.hom.app Y := by
  have hu := unit_conjugateEquiv a b α.inv X
  rw [h] at hu
  calc
    _ = (b.unit.app X ≫ R'.map (α.inv.app X)) ≫ R'.map t := by
      rw [b.homEquiv_unit, R'.map_comp, Category.assoc]
    _ = (a.unit.app X ≫ β.hom.app (L.obj X)) ≫ R'.map t :=
      congrArg (fun z => z ≫ R'.map t) hu.symm
    _ = a.unit.app X ≫ R.map t ≫ β.hom.app Y := by
      rw [Category.assoc, β.hom.naturality]
    _ = _ := by rw [a.homEquiv_unit, Category.assoc]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointIsoUnits
