import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleConcatenation
import Mathlib.Data.Fin.Tuple.Basic

/-! # Finite Tuple Concatenation -/

namespace OAI

namespace NumberTheory.PadicHodge.IntegralComparison.Cech.FiniteTupleConcatenation

/-! The signed concatenation calculation on the actual finite tuple
indices of the nonempty Čech nerve. -/

open scoped BigOperators

variable {ι V : Type*} [AddCommGroup V]

theorem ofFn_delete {n : ℕ} (f : Fin (n + 1) → ι) (i : Fin (n + 1)) :
    List.ofFn (f ∘ i.succAbove) = (List.ofFn f).eraseIdx i.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · conv_rhs => rw [List.ofFn_succ]
      rfl
    · conv_lhs => rw [List.ofFn_succ]
      conv_rhs => rw [List.ofFn_succ]
      simp only [Function.comp_apply, Fin.succ_succAbove_zero, Fin.succ_succAbove_succ,
        Fin.val_succ, List.eraseIdx_cons_succ]
      exact congrArg (f 0 :: ·) (ih (fun j => f j.succ) i)

def boundaryValue {n : ℕ} (f : List ι → V) (t : Fin (n + 1) → ι) : V :=
  ∑ i : Fin (n + 1), (-1 : ℤ)^i.val • f (List.ofFn (t ∘ i.succAbove))

theorem boundaryValue_eq {n : ℕ} (f : List ι → V) (t : Fin (n + 1) → ι) :
    boundaryValue f t = TupleConcatenation.boundaryValue f (List.ofFn t) := by
  simp only [boundaryValue, TupleConcatenation.boundaryValue,
    List.length_ofFn, ofFn_delete]
  exact Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ)^i • f ((List.ofFn t).eraseIdx i)) _

theorem boundary_append {m n : ℕ} (f : List ι → V)
    (a : Fin (m + 1) → ι) (b : Fin (n + 1) → ι) :
    TupleConcatenation.boundaryValue f (List.ofFn (Fin.append a b)) =
      boundaryValue (fun t => f (t ++ List.ofFn b)) a +
        (-1 : ℤ)^(m + 1) • boundaryValue (fun t => f (List.ofFn a ++ t)) b := by
  rw [List.ofFn_fin_append, TupleConcatenation.boundary_append,
    List.length_ofFn, boundaryValue_eq, boundaryValue_eq]

theorem internal_cancellation {m n : ℕ} (f : List ι → V)
    (a : Fin (m + 1) → ι) (b : Fin (n + 1) → ι) :
    (-1 : ℤ)^(m + 2) • boundaryValue (fun t => f (t ++ List.ofFn b)) a +
      (-1 : ℤ)^(m + 1) •
        TupleConcatenation.boundaryValue f (List.ofFn (Fin.append a b)) -
      boundaryValue (fun t => f (List.ofFn a ++ t)) b = 0 := by
  simpa only [boundaryValue_eq, List.ofFn_fin_append, List.length_ofFn] using
    TupleConcatenation.internal_cancellation f (List.ofFn a) (List.ofFn b)

end NumberTheory.PadicHodge.IntegralComparison.Cech.FiniteTupleConcatenation

namespace NumberTheory.PadicHodge.IntegralComparison.Cech.FiniteTupleConcatenation.PrismCancellation

/-! The four boundary cases of the signed concatenation prism,
with the exact finite tuple lengths of the original double complex. -/

variable {ι V : Type*} [AddCommGroup V]
open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleConcatenation

theorem singleton (a : Fin 1 → ι) : List.ofFn a = [a 0] := by
  simp only [List.ofFn_succ, List.ofFn_zero]

theorem zero (f : List ι → V) (a b : Fin 1 → ι) :
    TupleConcatenation.boundaryValue f (List.ofFn a ++ List.ofFn b) =
      f (List.ofFn b) - f (List.ofFn a) := by
  rw [singleton a, singleton b, List.singleton_append, TupleConcatenation.boundary_singleton_left]
  simp only [TupleConcatenation.boundaryValue, List.length_singleton, Finset.sum_range_one, pow_zero,
    one_smul, List.eraseIdx_cons_zero]

theorem left (f : List ι → V) (n : ℕ) (a : Fin 1 → ι) (b : Fin (n + 2) → ι) :
    TupleConcatenation.boundaryValue f (List.ofFn a ++ List.ofFn b) +
      TupleConcatenation.boundaryValue (fun l => f (List.ofFn a ++ l)) (List.ofFn b) =
        f (List.ofFn b) := by
  rw [singleton a, List.singleton_append, TupleConcatenation.boundary_singleton_left]
  simp only [List.singleton_append]
  abel

theorem right (f : List ι → V) (n : ℕ) (a : Fin (n + 2) → ι) (b : Fin 1 → ι) :
    (-1 : ℤ)^(n + 1) • TupleConcatenation.boundaryValue f (List.ofFn a ++ List.ofFn b) +
      (-1 : ℤ)^n • TupleConcatenation.boundaryValue (fun l => f (l ++ List.ofFn b)) (List.ofFn a) =
        -f (List.ofFn a) := by
  rw [singleton b, TupleConcatenation.boundary_singleton_right, List.length_ofFn, smul_add, smul_smul]
  have hs : (-1 : ℤ)^(n + 1) * (-1 : ℤ)^(n + 2) = -1 := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ (-1 : ℤ) (n + 1),
      ← mul_assoc, ← mul_pow]
    norm_num
  rw [hs, neg_one_zsmul, pow_succ, mul_neg_one, neg_smul]
  abel

theorem interior (f : List ι → V) (p q : ℕ)
    (a : Fin (p + 2) → ι) (b : Fin (q + 2) → ι) :
    (-1 : ℤ)^(p + 1) • TupleConcatenation.boundaryValue f (List.ofFn a ++ List.ofFn b) +
      ((-1 : ℤ)^p • TupleConcatenation.boundaryValue (fun l => f (l ++ List.ofFn b)) (List.ofFn a) +
        TupleConcatenation.boundaryValue (fun l => f (List.ofFn a ++ l)) (List.ofFn b)) = 0 := by
  rw [TupleConcatenation.boundary_append, List.length_ofFn, smul_add, smul_smul]
  have hs : (-1 : ℤ)^(p + 1) * (-1 : ℤ)^(p + 2) = -1 := by
    rw [show p + 2 = (p + 1) + 1 by omega, pow_succ (-1 : ℤ) (p + 1),
      ← mul_assoc, ← mul_pow]
    norm_num
  rw [hs, neg_one_zsmul, pow_succ, mul_neg_one, neg_smul]
  abel

end NumberTheory.PadicHodge.IntegralComparison.Cech.FiniteTupleConcatenation.PrismCancellation

end OAI
