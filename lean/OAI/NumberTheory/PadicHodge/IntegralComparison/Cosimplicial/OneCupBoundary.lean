import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.Cup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # One Cup Boundary -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.OneCupBoundary

noncomputable section

/-! Explicit boundaries for degree-one Alexander–Whitney products in
the actual alternating-coface complex. When two is invertible, the
square of every degree-one cocycle is an actual boundary. -/

open _root_.CategoryTheory
open scoped Simplicial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.Cup

universe u

theorem front_one_one : AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion 1 1 = SimplexCategory.δ (2 : Fin 3) := by
  ext i
  fin_cases i <;> rfl

theorem back_one_one : AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion 1 1 = SimplexCategory.δ (0 : Fin 3) := by
  ext i
  fin_cases i <;> rfl

variable (A : CosimplicialObject CommRingCat.{u})

theorem differential_one (x : A.obj ⦋1⦌) :
    Cup.differential A 1 x =
      A.map (SimplexCategory.δ (0 : Fin 3)) x -
        A.map (SimplexCategory.δ (1 : Fin 3)) x +
        A.map (SimplexCategory.δ (2 : Fin 3)) x := by
  simp [Cup.differential, Fin.sum_univ_succ, sub_eq_add_neg, add_assoc]

theorem cup_one_one (x y : A.obj ⦋1⦌) :
    Cup.cup A x y = A.map (SimplexCategory.δ (2 : Fin 3)) x *
      A.map (SimplexCategory.δ (0 : Fin 3)) y := by
  rw [Cup.cup, front_one_one, back_one_one]

theorem cocycle_middle (x : A.obj ⦋1⦌) (hx : Cup.differential A 1 x = 0) :
    A.map (SimplexCategory.δ (1 : Fin 3)) x =
      A.map (SimplexCategory.δ (0 : Fin 3)) x +
        A.map (SimplexCategory.δ (2 : Fin 3)) x := by
  rw [differential_one] at hx
  linear_combination -hx

theorem product_differential (x y : A.obj ⦋1⦌)
    (hx : Cup.differential A 1 x = 0) (hy : Cup.differential A 1 y = 0) :
    Cup.differential A 1 (x * y) = -(Cup.cup A x y + Cup.cup A y x) := by
  rw [differential_one, cup_one_one, cup_one_one]
  simp only [map_mul, cocycle_middle A x hx, cocycle_middle A y hy]
  ring

theorem square_differential (x : A.obj ⦋1⦌) (hx : Cup.differential A 1 x = 0) :
    Cup.differential A 1 (x * x) = -((2 : A.obj ⦋2⦌) * Cup.cup A x x) := by
  simpa only [two_mul] using product_differential A x x hx hx

theorem cup_sum_isBoundary (x y : A.obj ⦋1⦌)
    (hx : Cup.differential A 1 x = 0) (hy : Cup.differential A 1 y = 0) :
    ∃ z : A.obj ⦋1⦌, Cup.differential A 1 z = Cup.cup A x y + Cup.cup A y x := by
  refine ⟨-(x * y), ?_⟩
  have hneg (v : A.obj ⦋1⦌) : Cup.differential A 1 (-v) = -Cup.differential A 1 v := by
    simp only [Cup.differential, map_neg, smul_neg, Finset.sum_neg_distrib]
  rw [hneg, product_differential A x y hx hy, neg_neg]

theorem cup_self_isBoundary [Invertible (2 : A.obj ⦋1⦌)] [Invertible (2 : A.obj ⦋2⦌)]
    (x : A.obj ⦋1⦌) (hx : Cup.differential A 1 x = 0) :
    ∃ z : A.obj ⦋1⦌, Cup.differential A 1 z = Cup.cup A x x := by
  have hi (i : Fin 3) :
      A.map (SimplexCategory.δ i) (⅟(2 : A.obj ⦋1⦌)) = ⅟(2 : A.obj ⦋2⦌) := by
    symm
    apply invOf_eq_left_inv
    have h := congrArg (A.map (SimplexCategory.δ i)) (invOf_mul_self (2 : A.obj ⦋1⦌))
    simpa only [map_mul, map_ofNat, map_one] using h
  refine ⟨-(⅟(2 : A.obj ⦋1⦌)) * (x * x), ?_⟩
  calc
    Cup.differential A 1 (-(⅟(2 : A.obj ⦋1⦌)) * (x * x)) =
        -(⅟(2 : A.obj ⦋2⦌)) * Cup.differential A 1 (x * x) := by
      simp only [differential_one, map_mul, map_neg, hi]
      ring
    _ = -(⅟(2 : A.obj ⦋2⦌)) * -((2 : A.obj ⦋2⦌) * Cup.cup A x x) := by
      rw [square_differential A x hx]
    _ = Cup.cup A x x := by
      rw [neg_mul_neg, ← mul_assoc, invOf_mul_self, one_mul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.OneCupBoundary
