import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.OperationsMap

/-! # Associativity Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup

noncomputable section

/-! The associativity and commutativity diagrams after transport agree with the original mapped diagrams through invertible tensor comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Functor.LaxMonoidal

universe u

variable {S T : Scheme.{u}} {X : Over S} (D : Operations.FamilyGroupOperations X)
variable (F : Over S ⥤ Over T) [F.Monoidal]

theorem Operations.FamilyGroupOperations.map_assoc_left_formula :
    (D.map F).mul ▷ F.obj X ≫ (D.map F).mul =
      μ F X X ▷ F.obj X ≫ μ F (X ⊗ X) X ≫ F.map (D.mul ▷ X ≫ D.mul) := by
  simp only [Operations.FamilyGroupOperations.map, comp_whiskerRight, Category.assoc,
    μ_natural_left_assoc, Functor.map_comp]

theorem Operations.FamilyGroupOperations.map_assoc_right_formula :
    (α_ (F.obj X) (F.obj X) (F.obj X)).hom ≫ F.obj X ◁ (D.map F).mul ≫ (D.map F).mul =
      μ F X X ▷ F.obj X ≫ μ F (X ⊗ X) X ≫
        F.map ((α_ X X X).hom ≫ X ◁ D.mul ≫ D.mul) := by
  simp only [Operations.FamilyGroupOperations.map, whiskerLeft_comp, Category.assoc,
    μ_natural_right_assoc, Functor.map_comp]
  rw [← associativity_assoc]

theorem AssociativityMap.cartesianMonoidalFunctor_braiding (Y Z : Over S) :
    μ F Y Z ≫ F.map (β_ Y Z).hom = (β_ (F.obj Y) (F.obj Z)).hom ≫ μ F Z Y := by
  rw [← cancel_mono (Functor.Monoidal.μIso F Z Y).inv]
  ext <;> simp [← F.map_comp]

theorem Operations.FamilyGroupOperations.map_comm_formula :
    (β_ (F.obj X) (F.obj X)).hom ≫ (D.map F).mul =
      μ F X X ≫ F.map ((β_ X X).hom ≫ D.mul) := by
  dsimp only [Operations.FamilyGroupOperations.map]
  rw [Functor.map_comp, ← Category.assoc, ← AssociativityMap.cartesianMonoidalFunctor_braiding, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup
