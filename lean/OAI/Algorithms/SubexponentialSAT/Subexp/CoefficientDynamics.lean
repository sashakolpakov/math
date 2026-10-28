import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BinomialInterpolation

namespace OAI.Algorithms

/-!
# Division-free tests for the normalized binomial interpolant

The executable coefficient checker shifts a list by `a[j] + 2*a[j+1]`.
Its first entry after `t` shifts is the normalized binomial evaluation at
`t`. Thus no table of binomial coefficients is an input to the checker.
-/

namespace SubexponentialSAT.Subexp.CoefficientDynamics

open scoped BigOperators

variable {K : Type*}

section Ring

variable [CommRing K]

def shift : List K → List K
  | [] => []
  | a :: rest => (a + 2 * rest.getD 0 0) :: shift rest

@[simp] theorem shift_length (a : List K) : (shift a).length = a.length := by
  induction a <;> simp [shift, *]

@[simp] theorem shift_getD (a : List K) (j : ℕ) :
    (shift a).getD j 0 = a.getD j 0 + 2 * a.getD (j + 1) 0 := by
  induction a generalizing j with
  | nil => simp [shift]
  | cons x xs ih =>
      cases j with
      | zero => rfl
      | succ j =>
          change (shift xs).getD j 0 = xs.getD j 0 + 2 * xs.getD (j + 1) 0
          exact ih j

def shifts : ℕ → List K → List K
  | 0,a => a
  | n + 1,a => shifts n (shift a)

@[simp] theorem shifts_length (n : ℕ) (a : List K) : (shifts n a).length = a.length := by
  induction n generalizing a <;> simp [shifts, *]

theorem shifts_add (m n : ℕ) (a : List K) :
    shifts (m + n) a = shifts m (shifts n a) := by
  induction n generalizing a with
  | zero => simp [shifts]
  | succ n ih =>
      rw [Nat.add_succ]
      simp only [shifts]
      exact ih (shift a)

theorem shifts_succ_commute (n : ℕ) (a : List K) :
    shifts n (shift a) = shift (shifts n a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => exact ih (shift a)

def evaluate (a : List K) (t : ℕ) : K :=
  ∑ j ∈ Finset.range a.length, a.getD j 0 * 2 ^ j * (t.choose j : K)

theorem sum_shift (R t : ℕ) (a : ℕ → K) (hR : a R = 0) :
    (∑ j ∈ Finset.range R, (a j + 2 * a (j + 1)) * 2 ^ j * (t.choose j : K)) =
      ∑ j ∈ Finset.range R, a j * 2 ^ j * ((t + 1).choose j : K) := by
  cases R with
  | zero => simp
  | succ R =>
      have hsplit :
          (∑ j ∈ Finset.range (R + 1), (a j + 2 * a (j + 1)) * 2 ^ j * (t.choose j : K)) =
            (∑ j ∈ Finset.range (R + 1), a j * 2 ^ j * (t.choose j : K)) +
              ∑ j ∈ Finset.range (R + 1), a (j + 1) * 2 ^ (j + 1) * (t.choose j : K) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [pow_succ]
        ring
      rw [hsplit]
      rw [Finset.sum_range_succ' (fun j => a j * 2 ^ j * (t.choose j : K))]
      rw [Finset.sum_range_succ (fun j => a (j + 1) * 2 ^ (j + 1) * (t.choose j : K))]
      rw [Finset.sum_range_succ' (fun j => a j * 2 ^ j * ((t + 1).choose j : K))]
      simp only [hR,zero_mul,add_zero,pow_zero,Nat.choose_zero_right,Nat.cast_one,mul_one]
      simp_rw [Nat.choose_succ_succ,Nat.cast_add,mul_add]
      rw [Finset.sum_add_distrib]
      ring

theorem evaluate_shift (a : List K) (t : ℕ) : evaluate (shift a) t = evaluate a (t + 1) := by
  simp only [evaluate,shift_length,shift_getD]
  exact sum_shift a.length t (fun j => a.getD j 0)
    (List.getD_eq_default a 0 (le_refl _))

theorem evaluate_shifts (a : List K) (n t : ℕ) :
    evaluate (shifts n a) t = evaluate a (n + t) := by
  induction n generalizing a with
  | zero => simp [shifts]
  | succ n ih =>
      rw [shifts,ih,evaluate_shift]
      congr 1
      omega

@[simp] theorem evaluate_zero (a : List K) : evaluate a 0 = a.getD 0 0 := by
  cases a with
  | nil => simp [evaluate]
  | cons x xs =>
      rw [evaluate,List.length_cons,Finset.sum_range_succ']
      simp

theorem head_shifts (a : List K) (n : ℕ) :
    (shifts n a).getD 0 0 = evaluate a n := by
  simpa using evaluate_shifts a n 0

theorem head_shifts_add (a : List K) (m n : ℕ) :
    (shifts n (shifts m a)).getD 0 0 = evaluate a (m + n) := by
  rw [head_shifts,evaluate_shifts]

theorem evaluate_ofFn {R : ℕ} (a : Fin R → K) (t : ℕ) :
    evaluate (List.ofFn a) t = ∑ j : Fin R, a j * 2 ^ j.val * (t.choose j.val : K) := by
  unfold evaluate
  rw [List.length_ofFn]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt)]
  simp

end Ring

section Field

variable [Field K]

/-- Existence is used only to prove that the finite executable search will
succeed. It is not the implementation of coefficient selection. -/
theorem exists_normalized (h2 : (2 : K) ≠ 0) (A R : ℕ) :
    ∃ a : List K, a.length = R ∧
      ∀ d : Fin R, evaluate a (A + d.val) = (-1 : K) ^ (A + d.val) := by
  let c := BinomialInterpolation.parityCoefficients (K := K) A R
  refine ⟨List.ofFn (fun j : Fin R => c j / 2 ^ j.val),by simp,?_⟩
  intro d
  rw [evaluate_ofFn]
  calc
    _ = ∑ j : Fin R, c j * ((A + d.val).choose j.val : K) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [div_mul_cancel₀ _ (pow_ne_zero _ h2)]
    _ = _ := BinomialInterpolation.parityCoefficients_spec A R d

end Field

end SubexponentialSAT.Subexp.CoefficientDynamics

end OAI.Algorithms
