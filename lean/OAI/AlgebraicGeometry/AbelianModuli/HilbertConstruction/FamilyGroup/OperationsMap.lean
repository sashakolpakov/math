import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.Operations

/-! # Operations Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup

noncomputable section

/-! Actual transport of the three family operations through a Cartesian monoidal functor, without assuming any group laws before transport. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Functor.LaxMonoidal

universe u

variable {S T : Scheme.{u}} {X : Over S} (D : Operations.FamilyGroupOperations X)
variable (F : Over S ⥤ Over T) [F.Monoidal]

def Operations.FamilyGroupOperations.map : Operations.FamilyGroupOperations (F.obj X) where
  unit := ε F ≫ F.map D.unit
  mul := μ F X X ≫ F.map D.mul
  inv := F.map D.inv

structure Operations.FamilyGroupOperations.MappedLaws : Prop where
  one_mul : F.map (D.unit ▷ X ≫ D.mul) = F.map (λ_ X).hom
  mul_one : F.map (X ◁ D.unit ≫ D.mul) = F.map (ρ_ X).hom
  mul_assoc : F.map (D.mul ▷ X ≫ D.mul) = F.map ((α_ X X X).hom ≫ X ◁ D.mul ≫ D.mul)
  left_inv : F.map (lift D.inv (𝟙 X) ≫ D.mul) = F.map (toUnit X ≫ D.unit)
  right_inv : F.map (lift (𝟙 X) D.inv ≫ D.mul) = F.map (toUnit X ≫ D.unit)
  mul_comm : F.map ((β_ X X).hom ≫ D.mul) = F.map D.mul

theorem Operations.FamilyGroupOperations.map_one_mul_formula :
    (D.map F).unit ▷ F.obj X ≫ (D.map F).mul =
      ε F ▷ F.obj X ≫ μ F (𝟙_ (Over S)) X ≫ F.map (D.unit ▷ X ≫ D.mul) := by
  simp only [Operations.FamilyGroupOperations.map, comp_whiskerRight, Category.assoc,
    μ_natural_left_assoc, Functor.map_comp]

theorem Operations.FamilyGroupOperations.map_mul_one_formula :
    F.obj X ◁ (D.map F).unit ≫ (D.map F).mul =
      F.obj X ◁ ε F ≫ μ F X (𝟙_ (Over S)) ≫ F.map (X ◁ D.unit ≫ D.mul) := by
  simp only [Operations.FamilyGroupOperations.map, whiskerLeft_comp, Category.assoc,
    μ_natural_right_assoc, Functor.map_comp]

theorem Operations.FamilyGroupOperations.map_left_inv_formula :
    lift (D.map F).inv (𝟙 (F.obj X)) ≫ (D.map F).mul =
      F.map (lift D.inv (𝟙 X) ≫ D.mul) := by
  simp only [Operations.FamilyGroupOperations.map, ← F.map_id X, Functor.Monoidal.lift_μ_assoc,
    ← Functor.map_comp]

theorem Operations.FamilyGroupOperations.map_right_inv_formula :
    lift (𝟙 (F.obj X)) (D.map F).inv ≫ (D.map F).mul =
      F.map (lift (𝟙 X) D.inv ≫ D.mul) := by
  simp only [Operations.FamilyGroupOperations.map, ← F.map_id X, Functor.Monoidal.lift_μ_assoc,
    ← Functor.map_comp]

theorem Operations.FamilyGroupOperations.map_toUnit_unit_formula :
    toUnit (F.obj X) ≫ (D.map F).unit = F.map (toUnit X ≫ D.unit) := by
  simp only [Operations.FamilyGroupOperations.map, Functor.Monoidal.toUnit_ε_assoc, ← Functor.map_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup
