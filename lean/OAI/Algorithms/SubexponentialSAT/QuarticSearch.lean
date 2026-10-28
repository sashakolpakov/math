import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.FiniteField

namespace OAI.Algorithms

/-!
# Executable search for an irreducible quartic

The execution data are four field coefficients. Polynomial expressions occur
only in the correctness proof. Linear and quadratic trial division is performed
by fixed-size synthetic-division formulas.
-/
namespace SubexponentialSAT.QuarticSearch

open Polynomial
open scoped BigOperators

/-- Exhaustive explicit list of coefficient vectors. -/
def vectors {A : Type*} (alphabet : List A) : (d : ℕ) → List (Fin d → A)
  | 0 => [fun i => Fin.elim0 i]
  | d + 1 => alphabet.flatMap fun a => (vectors alphabet d).map (Fin.cons a)

theorem mem_vectors {A : Type*} (alphabet : List A) (h : ∀ a, a ∈ alphabet)
    (d : ℕ) (v : Fin d → A) : v ∈ vectors alphabet d := by
  induction d with
  | zero =>
      have he : v = fun i => Fin.elim0 i := by funext i; exact Fin.elim0 i
      simp [vectors, he]
  | succ d ih =>
      rw [vectors, List.mem_flatMap]
      refine ⟨v 0, h _, ?_⟩
      apply List.mem_map.mpr
      exact ⟨Fin.tail v, ih _, Fin.cons_self_tail v⟩

theorem length_vectors {A : Type*} (alphabet : List A) (d : ℕ) :
    (vectors alphabet d).length = alphabet.length ^ d := by
  induction d with
  | zero => simp [vectors]
  | succ d ih =>
      simp [vectors, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

/-- Mathematical interpretation; the search does not execute polynomial operations. -/
noncomputable def poly {F : Type*} [Semiring F] {d : ℕ} (c : Fin d → F) : F[X] :=
  X ^ d + ∑ i : Fin d, C (c i) * X ^ (i : ℕ)

/-- Polynomial interpretation commutes with a coefficient homomorphism. -/
theorem map_poly {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) {d : ℕ} (c : Fin d → R) :
    (poly c).map f = poly (fun i => f (c i)) := by
  simp [poly, Polynomial.map_sum]

/-- The input vector is exactly the low-degree coefficient vector. -/
theorem coeff_poly {R : Type*} [Semiring R] {d : ℕ}
    (c : Fin d → R) (i : Fin d) : (poly c).coeff (i : ℕ) = c i := by
  have hd : ((X : R[X])^d).coeff (i : ℕ) = 0 := by
    simp [coeff_X_pow, i.isLt.ne ]
  simp only [poly, coeff_add, finsetSum_coeff, hd, zero_add]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hj : (j : ℕ) ≠ (i : ℕ) := fun h => hji (Fin.ext h)
    simp [ Ne.symm hj]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

section PolynomialProof

variable {F : Type*} [CommRing F] [Nontrivial F]

omit [Nontrivial F] in
theorem poly_monic {d : ℕ} (c : Fin d → F) : (poly c).Monic :=
  monic_X_pow_add (degree_sum_fin_lt c)

@[simp] theorem poly_natDegree {d : ℕ} (c : Fin d → F) : (poly c).natDegree = d := by
  unfold poly
  rw [natDegree_add_eq_left_of_degree_lt]
  · simp
  · simpa using degree_sum_fin_lt c

omit [Nontrivial F] in
theorem poly_of_coeff {d : ℕ} (f : F[X]) (hm : f.Monic) (hd : f.natDegree = d) :
    poly (fun i : Fin d => f.coeff i) = f := by
  have he := f.as_sum_range_C_mul_X_pow
  rw [hd, Finset.sum_range_succ] at he
  have hc : f.coeff d = 1 := hd ▸ hm.coeff_natDegree
  rw [hc, C_1, one_mul] at he
  unfold poly
  have hs : (∑ i : Fin d, C (f.coeff (i : ℕ)) * X^(i : ℕ)) =
      ∑ i ∈ Finset.range d, C (f.coeff i) * X^i :=
    Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X^i) d
  change X^d + (∑ i : Fin d, C (f.coeff (i : ℕ)) * X^(i : ℕ)) = f
  rw [hs]
  exact (add_comm _ _).trans he.symm

omit [Nontrivial F] in
theorem poly_one (c : Fin 1 → F) : poly c = X + C (c 0) := by
  simp [poly]

omit [Nontrivial F] in
theorem poly_two (c : Fin 2 → F) : poly c = X^2 + C (c 1)*X + C (c 0) := by
  simp [poly, Fin.sum_univ_succ]
  ring

omit [Nontrivial F] in
theorem poly_three (c : Fin 3 → F) :
    poly c = X^3 + C (c 2)*X^2 + C (c 1)*X + C (c 0) := by
  simp [poly, Fin.sum_univ_succ]
  ring

omit [Nontrivial F] in
theorem poly_four (c : Fin 4 → F) :
    poly c = X^4 + C (c 3)*X^3 + C (c 2)*X^2 + C (c 1)*X + C (c 0) := by
  simp [poly, Fin.sum_univ_succ]
  ring

end PolynomialProof

section Synthetic

variable {F : Type*} [CommRing F]

/-- Quotient coefficients on division by `X+a`. -/
def linearQuotient (c : Fin 4 → F) (a : F) : Fin 3 → F :=
  let b₂ := c 3 - a
  let b₁ := c 2 - a*b₂
  let b₀ := c 1 - a*b₁
  ![b₀, b₁, b₂]

def linearRemainder (c : Fin 4 → F) (a : F) : F :=
  c 0 - a * linearQuotient c a 0

/-- Quotient coefficients on division by `X^2+a₁X+a₀`. -/
def quadraticQuotient (c : Fin 4 → F) (a : Fin 2 → F) : Fin 2 → F :=
  let b₁ := c 3 - a 1
  let b₀ := c 2 - a 0 - a 1*b₁
  ![b₀, b₁]

def quadraticRemainder (c : Fin 4 → F) (a : Fin 2 → F) : Fin 2 → F :=
  let b := quadraticQuotient c a
  ![c 0 - a 0*b 0, c 1 - (a 1*b 0 + a 0*b 1)]

end Synthetic

section SyntheticProof

variable {F : Type*} [Field F]

theorem linear_division_identity (c : Fin 4 → F) (a : F) :
    poly c = poly (![a] : Fin 1 → F) * poly (linearQuotient c a) +
      C (linearRemainder c a) := by
  rw [poly_four, poly_one, poly_three]
  simp [linearQuotient, linearRemainder, map_sub, map_mul]
  ring

theorem quadratic_division_identity (c : Fin 4 → F) (a : Fin 2 → F) :
    poly c = poly a * poly (quadraticQuotient c a) +
      (C (quadraticRemainder c a 1)*X + C (quadraticRemainder c a 0)) := by
  rw [poly_four, poly_two, poly_two]
  simp [quadraticQuotient, quadraticRemainder, map_sub, map_mul, map_add]
  ring

theorem linear_dvd_iff (c : Fin 4 → F) (a : F) :
    poly (![a] : Fin 1 → F) ∣ poly c ↔ linearRemainder c a = 0 := by
  constructor
  · intro hd
    have hr : poly (![a] : Fin 1 → F) ∣ C (linearRemainder c a) := by
      have h := dvd_sub hd (dvd_mul_right (poly (![a] : Fin 1 → F))
        (poly (linearQuotient c a)))
      rw [linear_division_identity c a] at h
      simpa using h
    by_contra hn
    exact (poly_monic (![a] : Fin 1 → F)).not_dvd_of_natDegree_lt
      (by simpa using hn) (by simp) hr
  · intro hr
    rw [linear_division_identity c a, hr, C_0, add_zero]
    exact dvd_mul_right _ _

theorem quadratic_dvd_iff (c : Fin 4 → F) (a : Fin 2 → F) :
    poly a ∣ poly c ↔ quadraticRemainder c a 0 = 0 ∧ quadraticRemainder c a 1 = 0 := by
  let r : F[X] := C (quadraticRemainder c a 1)*X + C (quadraticRemainder c a 0)
  have hdegree : r.natDegree < (poly a).natDegree := by
    rw [poly_natDegree]
    have hdeg : r.degree ≤ (1 : WithBot ℕ) := by
      exact (degree_add_le _ _).trans (max_le (degree_C_mul_X_le _)
        (degree_C_le.trans (by norm_num)))
    exact (natDegree_le_iff_degree_le.mpr hdeg).trans_lt (by norm_num)
  have hzero : r = 0 ↔ quadraticRemainder c a 0 = 0 ∧ quadraticRemainder c a 1 = 0 := by
    constructor
    · intro hr
      have h0 := congrArg (fun f : F[X] => f.coeff 0) hr
      have h1 := congrArg (fun f : F[X] => f.coeff 1) hr
      simpa [r] using And.intro h0 h1
    · rintro ⟨h0, h1⟩
      simp [r, h0, h1]
  rw [← hzero]
  constructor
  · intro hd
    by_contra hn
    have hr : poly a ∣ r := by
      have h := dvd_sub hd (dvd_mul_right (poly a) (poly (quadraticQuotient c a)))
      rw [quadratic_division_identity c a] at h
      simpa [r] using h
    exact (poly_monic a).not_dvd_of_natDegree_lt hn hdegree hr
  · intro hr
    rw [quadratic_division_identity c a]
    change poly a ∣ poly a * poly (quadraticQuotient c a) + r
    rw [hr, add_zero]
    exact dvd_mul_right _ _

/-- A monic quartic is irreducible exactly when these finite-size trial divisions fail. -/
theorem irreducible_iff_remainders (c : Fin 4 → F) :
    Irreducible (poly c) ↔
      (∀ a : F, linearRemainder c a ≠ 0) ∧
      (∀ a : Fin 2 → F, ¬(quadraticRemainder c a 0 = 0 ∧ quadraticRemainder c a 1 = 0)) := by
  have hp1 : poly c ≠ 1 := by
    intro he
    have h := congrArg Polynomial.natDegree he
    simp at h
  rw [(poly_monic c).irreducible_iff_lt_natDegree_lt hp1]
  constructor
  · intro h
    constructor
    · intro a ha
      exact h (poly (![a] : Fin 1 → F)) (poly_monic _) (by simp)
        ((linear_dvd_iff c a).mpr ha)
    · intro a ha
      exact h (poly a) (poly_monic _) (by simp)
        ((quadratic_dvd_iff c a).mpr ha)
  · rintro ⟨hlin, hquad⟩ q hqm hdeg hdiv
    have hd : q.natDegree = 1 ∨ q.natDegree = 2 := by
      simp only [poly_natDegree, Finset.mem_Ioc] at hdeg
      omega
    rcases hd with hd | hd
    · have he := poly_of_coeff q hqm hd
      have ht : (fun i : Fin 1 => q.coeff i) = ![q.coeff 0] := by
        funext i
        fin_cases i
        rfl
      rw [ht] at he
      apply hlin (q.coeff 0)
      apply (linear_dvd_iff c (q.coeff 0)).mp
      simpa [he] using hdiv
    · apply hquad (fun i : Fin 2 => q.coeff i)
      apply (quadratic_dvd_iff c _).mp
      simpa only [poly_of_coeff q hqm hd] using hdiv

end SyntheticProof


/-- The explicit residue representatives, in increasing order. -/
def elements (p : ℕ) : List (ZMod p) :=
  List.ofFn fun i : Fin p => (i.val : ZMod p)

@[simp] theorem length_elements (p : ℕ) : (elements p).length = p := by
  simp [elements]

theorem mem_elements (p : ℕ) [Fact p.Prime] (a : ZMod p) : a ∈ elements p := by
  apply List.mem_ofFn.mpr
  exact ⟨⟨a.val, ZMod.val_lt a⟩, by simp⟩

/-- Single linear-divisor test, implemented by field operations and equality. -/
def linearPass (p : ℕ) (c : Fin 4 → ZMod p) (a : ZMod p) : Bool :=
  decide (linearRemainder c a ≠ 0)

/-- Single quadratic-divisor test. -/
def quadraticPass (p : ℕ) (c : Fin 4 → ZMod p) (a : Fin 2 → ZMod p) : Bool :=
  decide (quadraticRemainder c a 0 ≠ 0 ∨ quadraticRemainder c a 1 ≠ 0)

/-- Test all monic linear and quadratic divisors using only field arithmetic. -/
def passes (p : ℕ) (c : Fin 4 → ZMod p) : Bool :=
  (elements p).all (linearPass p c) &&
  (vectors (elements p) 2).all (quadraticPass p c)

theorem passes_iff (p : ℕ) [Fact p.Prime] (c : Fin 4 → ZMod p) :
    passes p c = true ↔ Irreducible (poly c) := by
  rw [irreducible_iff_remainders]
  simp only [passes, Bool.and_eq_true, List.all_eq_true, linearPass, quadraticPass, decide_eq_true_eq]
  constructor
  · rintro ⟨hl, hq⟩
    refine ⟨fun a => hl a (mem_elements p a), ?_⟩
    intro a ha
    rcases hq a (mem_vectors (elements p) (mem_elements p) 2 a) with h0 | h1
    · exact h0 ha.1
    · exact h1 ha.2
  · rintro ⟨hl, hq⟩
    refine ⟨fun a _ => hl a, ?_⟩
    intro a _
    exact not_and_or.mp (hq a)

/-- Boolean list conjunction, counting the tests actually performed. -/
def checkAll {A : Type*} (test : A → Bool) : List A → Bool × ℕ
  | [] => (true, 0)
  | a :: as => if test a then
      let rest := checkAll test as
      (rest.1, rest.2 + 1)
    else (false, 1)

theorem checkAll_value {A : Type*} (test : A → Bool) (as : List A) :
    (checkAll test as).1 = as.all test := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      by_cases h : test a = true <;> simp [checkAll, h, ih]

theorem checkAll_count_le {A : Type*} (test : A → Bool) (as : List A) :
    (checkAll test as).2 ≤ as.length := by
  induction as with
  | nil => simp [checkAll]
  | cons a as ih =>
      by_cases h : test a = true <;> simp [checkAll, h] ; omega

/-- Evaluate both divisor lists and count the tests actually performed. -/
def evaluate (p : ℕ) (c : Fin 4 → ZMod p) : Bool × ℕ :=
  let linear := checkAll (linearPass p c) (elements p)
  let quadratic := checkAll (quadraticPass p c) (vectors (elements p) 2)
  (linear.1 && quadratic.1, linear.2 + quadratic.2)

theorem evaluate_value (p : ℕ) (c : Fin 4 → ZMod p) :
    (evaluate p c).1 = passes p c := by
  simp only [evaluate, checkAll_value, passes]

theorem evaluate_count_le (p : ℕ) (c : Fin 4 → ZMod p) :
    (evaluate p c).2 ≤ p + p^2 := by
  have hl := checkAll_count_le (linearPass p c) (elements p)
  have hq := checkAll_count_le (quadraticPass p c) (vectors (elements p) 2)
  simp only [length_vectors, length_elements] at hl hq
  exact Nat.add_le_add hl hq

/-- Ordered exhaustive search, counting both candidates and inner tests. -/
def scan {A : Type*} (evaluate : A → Bool × ℕ) : List A → Option A × ℕ × ℕ
  | [] => (none, 0, 0)
  | a :: as =>
      let current := evaluate a
      if current.1 then (some a, 1, current.2)
      else
        let rest := scan evaluate as
        (rest.1, rest.2.1 + 1, rest.2.2 + current.2)

theorem scan_value {A : Type*} (evaluate : A → Bool × ℕ) (as : List A) :
    (scan evaluate as).1 = as.find? (fun a => (evaluate a).1) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      by_cases h : (evaluate a).1 = true <;> simp [scan, h, ih]

theorem scan_candidates_le {A : Type*} (evaluate : A → Bool × ℕ) (as : List A) :
    (scan evaluate as).2.1 ≤ as.length := by
  induction as with
  | nil => simp [scan]
  | cons a as ih =>
      by_cases h : (evaluate a).1 = true <;> simp [scan, h] ; omega

theorem scan_tests_le {A : Type*} (evaluate : A → Bool × ℕ) (as : List A) (bound : ℕ)
    (h : ∀ a ∈ as, (evaluate a).2 ≤ bound) :
    (scan evaluate as).2.2 ≤ as.length * bound := by
  induction as with
  | nil => simp [scan]
  | cons a as ih =>
      have ha := h a List.mem_cons_self
      have ht := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
      by_cases hv : (evaluate a).1 = true <;> simp [scan, hv, Nat.add_mul] <;> omega

/-- Search result: coefficient vector, candidate count, divisor-test count. -/
def search (p : ℕ) : Option (Fin 4 → ZMod p) × ℕ × ℕ :=
  scan (evaluate p) (vectors (elements p) 4)

/-- Total executable coefficient selection. Prime moduli are proved below to succeed. -/
def coefficients (p : ℕ) : Fin 4 → ZMod p :=
  (search p).1.getD (fun _ => 0)

theorem search_candidates_le (p : ℕ) : (search p).2.1 ≤ p^4 := by
  simpa [search, length_vectors] using
    scan_candidates_le (evaluate p) (vectors (elements p) 4)

theorem search_tests_le (p : ℕ) : (search p).2.2 ≤ p^4 * (p + p^2) := by
  simpa [search, length_vectors] using
    scan_tests_le (evaluate p) (vectors (elements p) 4) (p+p^2)
      (fun c _ => evaluate_count_le p c)

theorem exists_passing (p : ℕ) [Fact p.Prime] :
    ∃ c ∈ vectors (elements p) 4, passes p c = true := by
  obtain ⟨f, hm, hi, hd⟩ := SubexponentialSAT.FiniteField.exists_monic_irreducible p 4 (by decide)
  let c : Fin 4 → ZMod p := fun i => f.coeff i
  refine ⟨c, mem_vectors (elements p) (mem_elements p) 4 c, ?_⟩
  apply (passes_iff p c).mpr
  simpa only [c, poly_of_coeff f hm hd] using hi

theorem search_ne_none (p : ℕ) [Fact p.Prime] : (search p).1 ≠ none := by
  intro hn
  have hh : (vectors (elements p) 4).find? (fun c => (evaluate p c).1) = none := by
    simpa only [search, scan_value] using hn
  obtain ⟨c, hc, hp⟩ := exists_passing p
  have hnop := List.find?_eq_none.mp hh c hc
  exact hnop (by simpa [evaluate_value] using hp)

theorem coefficients_irreducible (p : ℕ) [Fact p.Prime] :
    Irreducible (poly (coefficients p)) := by
  cases hs : (search p).1 with
  | none => exact False.elim (search_ne_none p hs)
  | some c =>
      have hf : (vectors (elements p) 4).find? (fun c => (evaluate p c).1) = some c := by
        simpa only [search, scan_value] using hs
      have hp := List.find?_some hf
      have hi := (passes_iff p c).mp (by simpa [evaluate_value] using hp)
      simpa [coefficients, hs] using hi

theorem coefficients_monic (p : ℕ) [Fact p.Prime] :
    (poly (coefficients p)).Monic := poly_monic _

theorem coefficients_natDegree (p : ℕ) [Fact p.Prime] :
    (poly (coefficients p)).natDegree = 4 := poly_natDegree _

/-- Executable coefficientwise lift into the prime-power base ring. -/
def liftedCoefficients (p μ : ℕ) : Fin 4 → ZMod (p^μ) :=
  fun i => ((coefficients p i).val : ZMod (p^μ))

end SubexponentialSAT.QuarticSearch

end OAI.Algorithms
