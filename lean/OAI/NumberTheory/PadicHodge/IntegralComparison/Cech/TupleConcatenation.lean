import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.NatInt
import Mathlib.Tactic.Abel

/-! # Tuple Concatenation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleConcatenation

/-! The signed tuple-concatenation identity underlying interchange of
the two Čech augmentations. Empty tuples are retained, so both edge
terms remain explicit. -/

open scoped BigOperators

variable {ι V : Type*} [AddCommGroup V]

def boundaryValue (f : List ι → V) (t : List ι) : V :=
  ∑ i ∈ Finset.range t.length, (-1 : ℤ)^i • f (t.eraseIdx i)

theorem boundary_append (f : List ι → V) (a b : List ι) :
    boundaryValue f (a ++ b) =
      boundaryValue (fun t => f (t ++ b)) a +
        (-1 : ℤ)^a.length • boundaryValue (fun t => f (a ++ t)) b := by
  unfold boundaryValue
  rw [List.length_append, Finset.sum_range_add, Finset.smul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [List.eraseIdx_append_of_lt_length (Finset.mem_range.mp hi)]
  · apply Finset.sum_congr rfl
    intro i _
    rw [List.eraseIdx_append_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      pow_add, mul_smul]

theorem boundary_singleton_left (f : List ι → V) (a : ι) (b : List ι) :
    boundaryValue f (a :: b) = f b - boundaryValue (fun t => f (a :: t)) b := by
  have h := boundary_append f [a] b
  simpa only [List.singleton_append, boundaryValue, List.length_singleton,
    Finset.sum_range_one, pow_zero, one_smul, List.eraseIdx_cons_zero,
    List.nil_append, pow_one, neg_one_zsmul, sub_eq_add_neg] using h

theorem boundary_singleton_right (f : List ι → V) (a : List ι) (b : ι) :
    boundaryValue f (a ++ [b]) = boundaryValue (fun t => f (t ++ [b])) a +
      (-1 : ℤ)^a.length • f a := by
  have h := boundary_append f a [b]
  simpa only [boundaryValue, List.length_singleton, Finset.sum_range_one,
    pow_zero, one_smul, List.eraseIdx_cons_zero, List.append_nil] using h

theorem internal_cancellation (f : List ι → V) (a b : List ι) :
    (-1 : ℤ)^(a.length+1) • boundaryValue (fun t => f (t ++ b)) a +
      (-1 : ℤ)^a.length • boundaryValue f (a ++ b) -
        boundaryValue (fun t => f (a ++ t)) b = 0 := by
  rw [boundary_append, smul_add, smul_smul, ← mul_pow]
  rw [show (-1 : ℤ) * (-1) = 1 by decide, one_pow, one_smul,
    pow_succ, mul_neg_one, neg_smul]
  abel

/-- The two end terms survive precisely on the two edges of the
unaugmented double Čech complex. This is the component equation for
the concatenation homotopy. -/
theorem prism_cancellation (f : List ι → V) (x y : ι) (a b : List ι) :
    (if a = [] then 0 else
      -((-1 : ℤ)^a.length • boundaryValue (fun t => f (t ++ y :: b)) (x :: a))) +
    (if b = [] then 0 else boundaryValue (fun t => f ((x :: a) ++ t)) (y :: b)) +
      (-1 : ℤ)^a.length • boundaryValue f ((x :: a) ++ y :: b) =
        (if a = [] then f (y :: b) else 0) -
          (if b = [] then f (x :: a) else 0) := by
  classical
  have sign : (-1 : ℤ)^a.length * (-1 : ℤ)^(a.length + 1) = -1 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    rw [show (-1 : ℤ) * (-1) = 1 by decide, one_pow, one_mul]
  have full : -((-1 : ℤ)^a.length •
        boundaryValue (fun t => f (t ++ y :: b)) (x :: a)) +
      boundaryValue (fun t => f ((x :: a) ++ t)) (y :: b) +
        (-1 : ℤ)^a.length • boundaryValue f ((x :: a) ++ y :: b) = 0 := by
    rw [boundary_append, List.length_cons, smul_add, smul_smul, sign, neg_one_zsmul]
    abel
  by_cases ha : a = [] <;> by_cases hb : b = []
  · subst a
    subst b
    simp [boundaryValue, Finset.sum_range_succ, sub_eq_add_neg]
  · simp only [ite_eq_left ha, ite_eq_right hb, zero_add, sub_zero]
    subst a
    simp only [List.length_nil, pow_zero, one_smul] at full ⊢
    have he : boundaryValue (fun t => f (t ++ y :: b)) [x] = f (y :: b) := by
      simp only [boundaryValue, List.length_singleton, Finset.sum_range_one,
        pow_zero, one_smul, List.eraseIdx_cons_zero, List.nil_append]
    rw [he] at full
    apply sub_eq_zero.mp
    convert full using 1
    abel
  · simp only [ite_eq_right ha, ite_eq_left hb, add_zero, zero_sub]
    subst b
    have he : boundaryValue (fun t => f ((x :: a) ++ t)) [y] = f (x :: a) := by
      simp only [boundaryValue, List.length_singleton, Finset.sum_range_one,
        pow_zero, one_smul, List.eraseIdx_cons_zero, List.append_nil]
    rw [he] at full
    apply sub_eq_zero.mp
    convert full using 1
    abel
  · simpa only [ite_eq_right ha, ite_eq_right hb, sub_zero] using full

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleConcatenation
