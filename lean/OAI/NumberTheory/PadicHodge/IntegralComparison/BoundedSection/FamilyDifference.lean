import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Family

/-! # Family Difference -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.FamilyDifference.Family

noncomputable section

/-!
# IntegralComparison: component formulas for the difference map of bounded section complexes
-/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustivePresheafSections

universe u v

variable {C : Type u} [Category.{v} C] (R : Type u) [CommRing R]
  (P : ℕ → ObjectProperty C) (hP : Monotone P) (M : ModuleCat.{u} R)
  (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Family.complex R P M K

def transition (n m : ℕ) (hnm : n ≤ m) :
    CountableProductHomology.component R F m ⟶ CountableProductHomology.component R F n where
  f i := ModuleCat.ofHom
    { toFun := ExhaustivePresheafSections.restrict P hP M (K.X i) n m hnm
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  comm' _ _ _ := ModuleCat.hom_ext (LinearMap.ext (fun _ => rfl))

def projection (n : ℕ) : ComplexExact.allComplex R P M K ⟶
    CountableProductHomology.component R F n :=
  (Family.productComplexIso R P M K).inv ≫ CountableProductHomology.projection R F n

theorem difference_projection (n : ℕ) :
    ComplexExact.difference R P hP M K ≫ projection R P M K n =
      projection R P M K n - projection R P M K (n + 1) ≫ transition R P hP M K n (n + 1) (Nat.le_succ n) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.FamilyDifference.Family
