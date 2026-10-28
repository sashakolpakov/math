import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.Operations

/-! # Commutative Group Law Equations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The commutative-group laws are a concrete finite list of proper-flat family morphism equations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

local instance CommutativeGroupLawEquations.groupEquationProductProper {S : Scheme.{u}} (X Y : Over S) [IsProper X.hom] [IsProper Y.hom] :
    IsProper (X ⊗ Y).hom := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom ≫ X.hom))

local instance CommutativeGroupLawEquations.groupEquationProductFlat {S : Scheme.{u}} (X Y : Over S) [Flat X.hom] [Flat Y.hom] :
    Flat (X ⊗ Y).hom := inferInstanceAs (Flat (pullback.fst X.hom Y.hom ≫ X.hom))

local instance CommutativeGroupLawEquations.groupEquationUnitProper {S : Scheme.{u}} : IsProper (𝟙_ (Over S)).hom :=
  inferInstanceAs (IsProper (𝟙 S))

local instance CommutativeGroupLawEquations.groupEquationUnitFlat {S : Scheme.{u}} : Flat (𝟙_ (Over S)).hom :=
  inferInstanceAs (Flat (𝟙 S))

variable {S : Scheme.{u}} {X : Over S} [IsProper X.hom] [Flat X.hom] (D : FamilyGroup.Operations.FamilyGroupOperations X)

def FamilyGroup.Operations.FamilyGroupOperations.equations : List (Finite.ProperEquationIdeals.ProperFamilyMorphismEquation S) :=
  [Finite.ProperEquationIdeals.ProperFamilyMorphismEquation.ofMaps (D.unit ▷ X ≫ D.mul) (λ_ X).hom,
   Finite.ProperEquationIdeals.ProperFamilyMorphismEquation.ofMaps (X ◁ D.unit ≫ D.mul) (ρ_ X).hom,
   Finite.ProperEquationIdeals.ProperFamilyMorphismEquation.ofMaps (D.mul ▷ X ≫ D.mul) ((α_ X X X).hom ≫ X ◁ D.mul ≫ D.mul),
   Finite.ProperEquationIdeals.ProperFamilyMorphismEquation.ofMaps (lift D.inv (𝟙 X) ≫ D.mul) (toUnit X ≫ D.unit),
   Finite.ProperEquationIdeals.ProperFamilyMorphismEquation.ofMaps (lift (𝟙 X) D.inv ≫ D.mul) (toUnit X ≫ D.unit),
   Finite.ProperEquationIdeals.ProperFamilyMorphismEquation.ofMaps ((β_ X X).hom ≫ D.mul) D.mul]

theorem FamilyGroup.Operations.FamilyGroupOperations.laws_iff_equations :
    D.Laws ↔ ∀ e ∈ D.equations, e.lhs = e.rhs := by
  simp only [FamilyGroup.Operations.FamilyGroupOperations.equations, List.forall_mem_cons]
  exact ⟨fun h => ⟨h.one_mul, h.mul_one, h.mul_assoc, h.left_inv, h.right_inv, h.mul_comm,
      fun e he => (List.not_mem_nil he).elim⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
