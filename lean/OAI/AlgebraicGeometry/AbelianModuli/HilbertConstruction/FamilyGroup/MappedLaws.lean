import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.AssociativityMap

/-! # Mapped Laws -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup

noncomputable section

/-! The six group laws hold on the transported family precisely when the six original diagrams become equal under the functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Functor.LaxMonoidal

universe u

variable {S T : Scheme.{u}} {X : Over S} (D : Operations.FamilyGroupOperations X)
variable (F : Over S ⥤ Over T) [F.Monoidal]

theorem Operations.FamilyGroupOperations.map_one_mul_iff :
    ((D.map F).unit ▷ F.obj X ≫ (D.map F).mul = (λ_ (F.obj X)).hom) ↔
      F.map (D.unit ▷ X ≫ D.mul) = F.map (λ_ X).hom := by
  rw [D.map_one_mul_formula, left_unitality F X]
  simpa only [Category.assoc] using
    (cancel_epi (ε F ▷ F.obj X ≫ μ F (𝟙_ (Over S)) X)
      (g := F.map (D.unit ▷ X ≫ D.mul)) (h := F.map (λ_ X).hom))

theorem Operations.FamilyGroupOperations.map_mul_one_iff :
    (F.obj X ◁ (D.map F).unit ≫ (D.map F).mul = (ρ_ (F.obj X)).hom) ↔
      F.map (X ◁ D.unit ≫ D.mul) = F.map (ρ_ X).hom := by
  rw [D.map_mul_one_formula, right_unitality F X]
  simpa only [Category.assoc] using
    (cancel_epi (F.obj X ◁ ε F ≫ μ F X (𝟙_ (Over S)))
      (g := F.map (X ◁ D.unit ≫ D.mul)) (h := F.map (ρ_ X).hom))

theorem Operations.FamilyGroupOperations.map_assoc_iff :
    ((D.map F).mul ▷ F.obj X ≫ (D.map F).mul =
      (α_ (F.obj X) (F.obj X) (F.obj X)).hom ≫ F.obj X ◁ (D.map F).mul ≫ (D.map F).mul) ↔
      F.map (D.mul ▷ X ≫ D.mul) = F.map ((α_ X X X).hom ≫ X ◁ D.mul ≫ D.mul) := by
  rw [D.map_assoc_left_formula, D.map_assoc_right_formula]
  simpa only [Category.assoc] using
    (cancel_epi (μ F X X ▷ F.obj X ≫ μ F (X ⊗ X) X)
      (g := F.map (D.mul ▷ X ≫ D.mul))
      (h := F.map ((α_ X X X).hom ≫ X ◁ D.mul ≫ D.mul)))

theorem Operations.FamilyGroupOperations.map_comm_iff :
    ((β_ (F.obj X) (F.obj X)).hom ≫ (D.map F).mul = (D.map F).mul) ↔
      F.map ((β_ X X).hom ≫ D.mul) = F.map D.mul := by
  rw [D.map_comm_formula]
  exact cancel_epi (μ F X X)

theorem Operations.FamilyGroupOperations.map_laws_iff : (D.map F).Laws ↔ D.MappedLaws F := by
  constructor
  · intro h
    refine ⟨(D.map_one_mul_iff F).mp h.one_mul, (D.map_mul_one_iff F).mp h.mul_one,
      (D.map_assoc_iff F).mp h.mul_assoc, ?_, ?_, (D.map_comm_iff F).mp h.mul_comm⟩
    · simpa only [D.map_left_inv_formula F, D.map_toUnit_unit_formula F] using h.left_inv
    · simpa only [D.map_right_inv_formula F, D.map_toUnit_unit_formula F] using h.right_inv
  · intro h
    refine ⟨(D.map_one_mul_iff F).mpr h.one_mul, (D.map_mul_one_iff F).mpr h.mul_one,
      (D.map_assoc_iff F).mpr h.mul_assoc, ?_, ?_, (D.map_comm_iff F).mpr h.mul_comm⟩
    · simpa only [D.map_left_inv_formula F, D.map_toUnit_unit_formula F] using h.left_inv
    · simpa only [D.map_right_inv_formula F, D.map_toUnit_unit_formula F] using h.right_inv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup
