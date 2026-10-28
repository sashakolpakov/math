import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProperEquationIdeals
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Operations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Multiplication, unit, and inversion are actual family morphisms; six explicit finite diagrams express the commutative-group laws. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

structure FamilyGroup.Operations.FamilyGroupOperations {S : Scheme.{u}} (X : Over S) where
  unit : 𝟙_ (Over S) ⟶ X
  mul : X ⊗ X ⟶ X
  inv : X ⟶ X

structure FamilyGroup.Operations.FamilyGroupOperations.Laws {S : Scheme.{u}} {X : Over S} (D : FamilyGroup.Operations.FamilyGroupOperations X) : Prop where
  one_mul : D.unit ▷ X ≫ D.mul = (λ_ X).hom
  mul_one : X ◁ D.unit ≫ D.mul = (ρ_ X).hom
  mul_assoc : D.mul ▷ X ≫ D.mul = (α_ X X X).hom ≫ X ◁ D.mul ≫ D.mul
  left_inv : lift D.inv (𝟙 X) ≫ D.mul = toUnit X ≫ D.unit
  right_inv : lift (𝟙 X) D.inv ≫ D.mul = toUnit X ≫ D.unit
  mul_comm : (β_ X X).hom ≫ D.mul = D.mul

@[instance_reducible] def FamilyGroup.Operations.FamilyGroupOperations.groupObj {S : Scheme.{u}} {X : Over S}
    (D : FamilyGroup.Operations.FamilyGroupOperations X) (h : D.Laws) : GrpObj X where
  one := D.unit
  mul := D.mul
  inv := D.inv
  one_mul := h.one_mul
  mul_one := h.mul_one
  mul_assoc := h.mul_assoc
  left_inv := h.left_inv
  right_inv := h.right_inv

theorem FamilyGroup.Operations.FamilyGroupOperations.groupObj_comm {S : Scheme.{u}} {X : Over S}
    (D : FamilyGroup.Operations.FamilyGroupOperations X) (h : D.Laws) : letI := D.groupObj h; IsCommMonObj X := by
  let : GrpObj X := D.groupObj h
  exact ⟨h.mul_comm⟩

def Finite.ProperEquationIdeals.ProperFamilyMorphismEquation.ofMaps {S : Scheme.{u}} {X Y : Over S}
    [IsProper X.hom] [Flat X.hom] [IsSeparated Y.hom] (u v : X ⟶ Y) : Finite.ProperEquationIdeals.ProperFamilyMorphismEquation S where
  source := X
  target := Y
  proper := inferInstance
  flat := inferInstance
  separated := inferInstance
  lhs := u
  rhs := v

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
