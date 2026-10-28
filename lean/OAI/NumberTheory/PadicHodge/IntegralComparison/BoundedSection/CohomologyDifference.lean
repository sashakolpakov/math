import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.FamilyDifference
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ProductCohomology

/-! # Cohomology Difference -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.CohomologyDifference

noncomputable section

/-!
# IntegralComparison: cohomology of the actual bounded-section difference operator
-/

open _root_.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] (R : Type u) [CommRing R]
  (P : ℕ → ObjectProperty C) (hP : Monotone P) (M : ModuleCat.{u} R)
  (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Family.complex R P M K
local notation "d" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.ComplexExact.difference R P hP M K
local notation "t" => fun n => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.FamilyDifference.Family.transition R P hP M K n (n + 1) (Nat.le_succ n)

theorem product_difference_projection (n : ℕ) :
    d ≫ CountableProductHomology.projection R F n =
      CountableProductHomology.projection R F n - CountableProductHomology.projection R F (n + 1) ≫ t n := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem homology_difference_epi (i : ℕ)
    [∀ n, Finite ((CountableProductHomology.component R F n).homology i)] :
    Epi (HomologicalComplex.homologyMap d i) :=
  IntegralComparison.Finite.ProductCohomology.epi R F d t (product_difference_projection R P hP M K) i

theorem difference_apply (i : ℕ) (x : ∀ n, (CountableProductHomology.component R F n).homology i) (n : ℕ) :
    CountableCohomologyDifference.difference R F d i x n =
      x n - HomologicalComplex.homologyMap (t n) i (x (n + 1)) :=
  CountableCohomologyDifference.difference_apply R F d t (product_difference_projection R P hP M K) i x n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.CohomologyDifference
