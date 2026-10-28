import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedMonoidHomEquations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.Operations

/-! # Monoid Hom Equations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MonoidHomEquations

noncomputable section

/-! Preservation of multiplication and identity is a finite list of equations from proper flat sources, with exact tests after every base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

local instance monoidHomProductProper {S : Scheme.{u}} (X Y : Over S) [IsProper X.hom] [IsProper Y.hom] :
    IsProper (X ⊗ Y).hom := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom ≫ X.hom))

local instance monoidHomProductFlat {S : Scheme.{u}} (X Y : Over S) [Flat X.hom] [Flat Y.hom] :
    Flat (X ⊗ Y).hom := inferInstanceAs (Flat (pullback.fst X.hom Y.hom ≫ X.hom))

local instance monoidHomUnitProper {S : Scheme.{u}} : IsProper (𝟙_ (Over S)).hom :=
  inferInstanceAs (IsProper (𝟙 S))

local instance monoidHomUnitFlat {S : Scheme.{u}} : Flat (𝟙_ (Over S)).hom :=
  inferInstanceAs (Flat (𝟙 S))

variable {S : Scheme.{u}} {X Y : Over S} [IsProper X.hom] [Flat X.hom] [IsSeparated Y.hom]
variable [MonObj X] [MonObj Y] (f : X ⟶ Y)

def familyMonoidHomEquations : List (Finite.ProperEquationIdeals.ProperFamilyMorphismEquation S) :=
  [Finite.ProperEquationIdeals.ProperFamilyMorphismEquation.ofMaps (η[X] ≫ f) η[Y],
   Finite.ProperEquationIdeals.ProperFamilyMorphismEquation.ofMaps (μ[X] ≫ f) ((f ⊗ₘ f) ≫ μ[Y])]

theorem familyMonoidHomEquations_baseChange_iff {T : Scheme.{u}} (c : T ⟶ S) :
    IsMonHom ((Over.pullback c).map f) ↔
      ∀ e ∈ familyMonoidHomEquations f, (Over.pullback c).map e.lhs = (Over.pullback c).map e.rhs := by
  rw [MappedMonoidHomEquations.mappedMonoidHom_iff]
  simp only [familyMonoidHomEquations, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true]
  rfl

def familyMonoidHomIdeal [IsLocallyNoetherian S] : S.IdealSheafData :=
  Finite.ProperEquationIdeals.properEquationListIdeal (familyMonoidHomEquations f)

theorem familyMonoidHomIdeal_test [IsLocallyNoetherian S] {T : Scheme.{u}} (c : T ⟶ S) :
    (familyMonoidHomIdeal f).comap c = ⊥ ↔ IsMonHom ((Over.pullback c).map f) :=
  (Finite.ProperEquationIdeals.properEquationListIdeal_test (familyMonoidHomEquations f) c).trans
    (familyMonoidHomEquations_baseChange_iff f c).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MonoidHomEquations
