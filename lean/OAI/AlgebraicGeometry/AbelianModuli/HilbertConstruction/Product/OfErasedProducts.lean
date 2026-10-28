import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Of Erased Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.OfErasedProducts

noncomputable section

/-! In the product of all products omitting one index, every factor
occurs exactly card κ minus one times. -/
open scoped BigOperators Classical
universe u v

theorem product_of_erased_products {κ : Type u} [Fintype κ] {M : Type v} [CommMonoid M]
    (x : κ → M) :
    (∏ i : κ, ∏ j ∈ (Finset.univ : Finset κ).erase i, x j) =
      (∏ j : κ, x j) ^ (Fintype.card κ - 1) := by
  let F := fun i j : κ => if j = i then 1 else x j
  have hrow (i : κ) : (∏ j, F i j) = ∏ j ∈ (Finset.univ : Finset κ).erase i, x j := by
    rw [← Finset.prod_erase_mul (Finset.univ : Finset κ) (F i) (Finset.mem_univ i)]
    simp only [F, ite_eq_left rfl, mul_one]
    apply Finset.prod_congr rfl
    intro j hj
    exact ite_eq_right (Finset.mem_erase.mp hj).1
  have hcol (j : κ) : (∏ i, F i j) = x j ^ (Fintype.card κ - 1) := by
    rw [← Finset.prod_erase_mul (Finset.univ : Finset κ) (fun i => F i j) (Finset.mem_univ j)]
    simp only [F, ite_eq_left rfl, mul_one]
    have he : (∏ i ∈ (Finset.univ : Finset κ).erase j, if j = i then 1 else x j) =
        ∏ _i ∈ (Finset.univ : Finset κ).erase j, x j := by
      apply Finset.prod_congr rfl
      intro i hi
      exact ite_eq_right (Ne.symm (Finset.mem_erase.mp hi).1)
    rw [he, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]
  calc
    _ = ∏ i, ∏ j, F i j := by simp only [hrow]
    _ = ∏ j, ∏ i, F i j := Finset.prod_comm
    _ = ∏ j, x j ^ (Fintype.card κ - 1) := by simp only [hcol]
    _ = _ := Finset.prod_pow _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.OfErasedProducts
