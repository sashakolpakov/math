import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BinomialInterpolation

namespace OAI.Algorithms

/-!
# Executable finite search for binomial interpolation coefficients

Execution uses an explicit residue alphabet, tuple enumeration, and equation
tests. The determinant-one interpolation theorem is used only to prove that
the search succeeds. No inverse or choice operator occurs in the algorithm.
-/

namespace SubexponentialSAT.Subexp.CoefficientSearch

open scoped BigOperators

section FiniteEnumeration

variable {α β : Type*}

/-- Enumerate all fixed-length tuples over a given finite alphabet. -/
def tuples (alphabet : List α) : (R : ℕ) → List (Fin R → α)
  | 0 => [fun i => Fin.elim0 i]
  | R + 1 =>
    let previous := tuples alphabet R
    alphabet.flatMap (fun a => previous.map (Fin.cons a))

theorem length_flatMap_uniform (l : List α) (f : α → List β) (n : ℕ)
    (h : ∀ a ∈ l, (f a).length = n) :
    (l.flatMap f).length = l.length * n := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]
    rw [Nat.succ_mul, Nat.add_comm]

@[simp] theorem tuples_length (alphabet : List α) (R : ℕ) :
    (tuples alphabet R).length = alphabet.length ^ R := by
  induction R with
  | zero => simp [tuples]
  | succ R ih =>
    rw [tuples, length_flatMap_uniform alphabet _ (alphabet.length ^ R)]
    · simp [Nat.pow_succ, Nat.mul_comm]
    · intro a _
      simpa using ih

theorem mem_tuples (alphabet : List α) (hall : ∀ a : α, a ∈ alphabet)
    (R : ℕ) (v : Fin R → α) : v ∈ tuples alphabet R := by
  induction R with
  | zero =>
    have hv : v = fun i => Fin.elim0 i := by
      funext i
      exact Fin.elim0 i
    simp [tuples, hv]
  | succ R ih =>
    apply List.mem_flatMap.mpr
    refine ⟨v 0, hall (v 0), List.mem_map.mpr ?_⟩
    exact ⟨Fin.tail v, ih (Fin.tail v), Fin.cons_self_tail v⟩

end FiniteEnumeration

section MeasuredSearch

variable {α : Type*}

/-- Short-circuit conjunction with an exact count of predicate evaluations. -/
def checkAll (test : α → Bool) : List α → Bool × ℕ
  | [] => (true, 0)
  | a :: as =>
    if test a then
      let remaining := checkAll test as
      (remaining.1, remaining.2 + 1)
    else (false, 1)

theorem checkAll_true_iff (test : α → Bool) (as : List α) :
    (checkAll test as).1 = true ↔ ∀ a ∈ as, test a = true := by
  induction as with
  | nil => simp [checkAll]
  | cons a as ih =>
    cases h : test a <;> simp [checkAll, h, ih]

theorem checkAll_tests_le (test : α → Bool) (as : List α) :
    (checkAll test as).2 ≤ as.length := by
  induction as with
  | nil => simp [checkAll]
  | cons a as ih =>
    cases h : test a with
    | false => simp [checkAll, h]
    | true => simpa [checkAll, h] using Nat.add_le_add_right ih 1

/-- Search result and the actual numbers of candidates and equations tested. -/
structure Report (α : Type*) where
  result : Option α
  candidatesTested : ℕ
  equationsTested : ℕ

/-- Return the first successful candidate, keeping both counters. -/
def scan (test : α → Bool × ℕ) : List α → Report α
  | [] => ⟨none, 0, 0⟩
  | a :: as =>
    let checked := test a
    if checked.1 then ⟨some a, 1, checked.2⟩
    else
      let remaining := scan test as
      ⟨remaining.result, remaining.candidatesTested + 1,
        remaining.equationsTested + checked.2⟩

theorem scan_result (test : α → Bool × ℕ) (as : List α) :
    (scan test as).result = as.find? (fun a => (test a).1) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases h : (test a).1 <;> simp [scan, h, List.find?, ih]

theorem scan_candidates_le (test : α → Bool × ℕ) (as : List α) :
    (scan test as).candidatesTested ≤ as.length := by
  induction as with
  | nil => simp [scan]
  | cons a as ih =>
    cases h : (test a).1 with
    | false => simpa [scan, h] using Nat.add_le_add_right ih 1
    | true => simp [scan, h]

theorem scan_equations_le (test : α → Bool × ℕ) (as : List α) (R : ℕ)
    (hcost : ∀ a ∈ as, (test a).2 ≤ R) :
    (scan test as).equationsTested ≤ R * as.length := by
  induction as with
  | nil => simp [scan]
  | cons a as ih =>
    have ha : (test a).2 ≤ R := hcost a (by simp)
    have hi := ih (fun b hb => hcost b (by simp [hb]))
    cases h : (test a).1 with
    | false =>
      simpa [scan, h, Nat.mul_succ] using Nat.add_le_add hi ha
    | true =>
      simp only [scan, h, ↓reduceIte, List.length_cons]
      exact ha.trans (by rw [Nat.mul_succ]; exact Nat.le_add_left _ _)

end MeasuredSearch

/-- Explicit enumeration of the residue labels 0,...,p-1. -/
def alphabet (p : ℕ) : List (ZMod p) :=
  (List.finRange p).map (fun a => (a.val : ZMod p))

@[simp] theorem alphabet_length (p : ℕ) : (alphabet p).length = p := by
  simp [alphabet]

theorem mem_alphabet (p : ℕ) (hp : 0 < p) (a : ZMod p) : a ∈ alphabet p := by
  let _ : NeZero p := ⟨Nat.ne_of_gt hp⟩
  apply List.mem_map.mpr
  exact ⟨⟨a.val, ZMod.val_lt a⟩, List.mem_finRange _, ZMod.natCast_zmod_val a⟩

/-- The finite system specifying the desired parity interpolant. -/
def Equations (p A R : ℕ) (c : Fin R → ZMod p) : Prop :=
  ∀ d : Fin R, (∑ j : Fin R, c j * ((A + d.val).choose j.val : ZMod p)) =
    (-1 : ZMod p) ^ (A + d.val)

/-- One decidable equation test. -/
def equationTest (p A R : ℕ) (c : Fin R → ZMod p) (d : Fin R) : Bool :=
  decide ((∑ j : Fin R, c j * ((A + d.val).choose j.val : ZMod p)) =
    (-1 : ZMod p) ^ (A + d.val))

/-- Test all R equations, counting those actually evaluated. -/
def checkVector (p A R : ℕ) (c : Fin R → ZMod p) : Bool × ℕ :=
  checkAll (equationTest p A R c) (List.finRange R)

theorem checkVector_true_iff (p A R : ℕ) (c : Fin R → ZMod p) :
    (checkVector p A R c).1 = true ↔ Equations p A R c := by
  simp [checkVector, checkAll_true_iff, Equations, equationTest]

theorem checkVector_tests_le (p A R : ℕ) (c : Fin R → ZMod p) :
    (checkVector p A R c).2 ≤ R := by
  simpa [checkVector] using
    checkAll_tests_le (equationTest p A R c) (List.finRange R)

/-- Finite search: the only candidates are the p^R explicitly enumerated
coefficient vectors, independent of the instance dimension D. -/
def search (p A R : ℕ) : Report (Fin R → ZMod p) :=
  scan (checkVector p A R) (tuples (alphabet p) R)

/-- The returned candidate is exactly the first one accepted by the test. -/
theorem search_result_eq_find (p A R : ℕ) :
    (search p A R).result =
      (tuples (alphabet p) R).find? (fun c => (checkVector p A R c).1) :=
  scan_result _ _

theorem search_candidates_le (p A R : ℕ) :
    (search p A R).candidatesTested ≤ p ^ R := by
  simpa [search] using
    scan_candidates_le (checkVector p A R) (tuples (alphabet p) R)

theorem search_equations_le (p A R : ℕ) :
    (search p A R).equationsTested ≤ R * p ^ R := by
  simpa [search] using
    scan_equations_le (checkVector p A R) (tuples (alphabet p) R) R
      (fun c _ => checkVector_tests_le p A R c)

/-- The search succeeds because the determinant-one binomial matrix
guarantees that its finite candidate list contains a solution. -/
theorem search_success (p A R : ℕ) (hp : 0 < p) :
    ∃ c, (search p A R).result = some c ∧ Equations p A R c := by
  let witness : Fin R → ZMod p :=
    BinomialInterpolation.parityCoefficients A R
  have hw : Equations p A R witness :=
    fun d => BinomialInterpolation.parityCoefficients_spec A R d
  have hm : witness ∈ tuples (alphabet p) R :=
    mem_tuples (alphabet p) (mem_alphabet p hp) R witness
  have ht : (checkVector p A R witness).1 = true :=
    (checkVector_true_iff p A R witness).mpr hw
  have hf := scan_result (checkVector p A R) (tuples (alphabet p) R)
  change (search p A R).result = _ at hf
  cases hr : (search p A R).result with
  | none =>
    rw [hr] at hf
    have hn := List.find?_eq_none.mp hf.symm
    exact False.elim (hn witness hm ht)
  | some c =>
    refine ⟨c, rfl, (checkVector_true_iff p A R c).mp ?_⟩
    rw [hr] at hf
    exact List.find?_some (p := fun a => (checkVector p A R a).1) (a := c) hf.symm

/-- Executable coefficient selection. The zero fallback is unreachable for
positive p, as proved below. -/
def coefficients (p A R : ℕ) : Fin R → ZMod p :=
  (search p A R).result.getD (fun _ => 0)

theorem coefficients_spec (p A R : ℕ) (hp : 0 < p) :
    Equations p A R (coefficients p A R) := by
  obtain ⟨c, hc, he⟩ := search_success p A R hp
  simpa [coefficients, hc] using he

/-- Uniqueness identifies the executable search result with the previously
verified inverse-defined coefficients. The inverse is not executed. -/
theorem coefficients_eq_parity (p A R : ℕ) (hp : 0 < p) :
    coefficients p A R =
      BinomialInterpolation.parityCoefficients (K := ZMod p) A R := by
  exact (BinomialInterpolation.existsUnique_binomial_interpolation
    (K := ZMod p) A R (fun d => (-1 : ZMod p) ^ (A + d.val))).unique
      (coefficients_spec p A R hp)
      (fun d => BinomialInterpolation.parityCoefficients_spec A R d)

/-- Executable zero extension matching the natural-number-indexed matrix
construction. -/
def coefficientsNat (p A R j : ℕ) : ZMod p :=
  if h : j < R then coefficients p A R ⟨j, h⟩ else 0

@[simp] theorem coefficientsNat_fin (p A R : ℕ) (j : Fin R) :
    coefficientsNat p A R j.val = coefficients p A R j := by
  simp [coefficientsNat, j.isLt]

theorem coefficientsNat_eq_zero (p A R j : ℕ) (hj : R ≤ j) :
    coefficientsNat p A R j = 0 := by
  simp [coefficientsNat, Nat.not_lt.mpr hj]

theorem sum_range_coefficientsNat (p A R w : ℕ) :
    (∑ j ∈ Finset.range R, coefficientsNat p A R j * (w.choose j : ZMod p)) =
      ∑ j : Fin R, coefficients p A R j * (w.choose j.val : ZMod p) := by
  simpa only [coefficientsNat_fin] using
    (Fin.sum_univ_eq_sum_range
      (fun j : ℕ => coefficientsNat p A R j * (w.choose j : ZMod p)) R).symm

theorem coefficientsNat_spec (p A R : ℕ) (hp : 0 < p) (d : Fin R) :
    (∑ j ∈ Finset.range R,
      coefficientsNat p A R j * ((A + d.val).choose j : ZMod p)) =
        (-1 : ZMod p) ^ (A + d.val) := by
  rw [sum_range_coefficientsNat]
  exact coefficients_spec p A R hp d

/-- The selected coefficients satisfy the required equation at every
integer weight in the interval, even when R exceeds p. -/
theorem coefficientsNat_spec_of_mem (p A R w : ℕ) (hp : 0 < p)
    (hA : A ≤ w) (hR : w < A + R) :
    (∑ j ∈ Finset.range R, coefficientsNat p A R j * (w.choose j : ZMod p)) =
      (-1 : ZMod p) ^ w := by
  let d : Fin R :=
    ⟨w - A, Nat.sub_lt_right_of_lt_add hA (by simpa [Nat.add_comm] using hR)⟩
  have hd : A + d.val = w := Nat.add_sub_of_le hA
  simpa only [hd] using coefficientsNat_spec p A R hp d

end SubexponentialSAT.Subexp.CoefficientSearch

end OAI.Algorithms
