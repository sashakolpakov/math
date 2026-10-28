import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BinomialInterpolation

namespace OAI.Algorithms

/-!
# Executable truncated elementary-symmetric recurrence

The executable routines below traverse finite coefficient lists. They do not
enumerate subsets. The coefficient semiring may be noncommutative, in
particular a matrix semiring or a semiring of linear endomorphisms.

The measured routines execute the same recurrence while recording one
addition and one multiplication per retained coefficient. This is an
arithmetic-operation count, not a claim about a bit-machine implementation.
-/

namespace SubexponentialSAT.Subexp.Elementary

open scoped BigOperators

section Recurrence

variable {S : Type*} [Semiring S]

/-- One coefficient-list pass. The second argument is the preceding old
coefficient; at the beginning of a pass it is zero. -/
def update (a previous : S) : List S → List S
  | [] => []
  | b :: bs => (b + a * previous) :: update a b bs

/-- The retained coefficients of the constant polynomial one. -/
def initial : ℕ → List S
  | 0 => []
  | R + 1 => 1 :: List.replicate R 0

/-- Compute the first R elementary coefficients by successive list passes.
The tail is processed first, fixing an order even without commutativity. -/
def coefficients (R : ℕ) : List S → List S
  | [] => initial R
  | a :: as => update a 0 (coefficients R as)

@[simp] theorem length_update (a previous : S) (bs : List S) :
    (update a previous bs).length = bs.length := by
  induction bs generalizing previous with
  | nil => rfl
  | cons b bs ih => simp [update, ih]

@[simp] theorem length_initial (R : ℕ) :
    (initial (S := S) R).length = R := by
  cases R <;> simp [initial]

@[simp] theorem length_coefficients (R : ℕ) (as : List S) :
    (coefficients R as).length = R := by
  induction as with
  | nil => exact length_initial R
  | cons a as ih => simpa [coefficients] using ih

theorem getD_update (a previous : S) (bs : List S) (j : ℕ)
    (hj : j < bs.length) :
    (update a previous bs).getD j 0 =
      bs.getD j 0 + a * (if j = 0 then previous else bs.getD (j - 1) 0) := by
  induction bs generalizing previous j with
  | nil => simp at hj
  | cons b bs ih =>
    cases j with
    | zero => simp [update]
    | succ j =>
      have h : j < bs.length := Nat.lt_of_succ_lt_succ hj
      have hi := ih b j h
      cases j <;> simpa [update] using hi

theorem getD_initial (R j : ℕ) (hj : j < R) :
    (initial (S := S) R).getD j 0 = if j = 0 then 1 else 0 := by
  cases R with
  | zero => simp at hj
  | succ R => cases j <;> simp [initial]

/-- Exact coefficient recurrence, including the zero-degree boundary. -/
theorem getD_coefficients_cons (R : ℕ) (a : S) (as : List S) (j : ℕ)
    (hj : j < R) :
    (coefficients R (a :: as)).getD j 0 =
      (coefficients R as).getD j 0 +
        a * (if j = 0 then 0 else (coefficients R as).getD (j - 1) 0) := by
  exact getD_update a 0 _ j (by simpa using hj)

/-- The generating polynomial specifying the ordered elementary coefficients.
Only the specification uses polynomials; the executable routine uses lists. -/
noncomputable def generatingPolynomial : List S → Polynomial S
  | [] => 1
  | a :: as => (1 + Polynomial.C a * Polynomial.X) * generatingPolynomial as

/-- The executable list agrees with the first R coefficients of the generating
polynomial, for an arbitrary possibly noncommutative coefficient semiring. -/
theorem coefficients_eq_polynomial (R : ℕ) (as : List S) (j : ℕ) (hj : j < R) :
    (coefficients R as).getD j 0 = (generatingPolynomial as).coeff j := by
  induction as generalizing j with
  | nil =>
    rw [coefficients, generatingPolynomial, getD_initial R j hj]
    simp [Polynomial.coeff_one]
  | cons a as ih =>
    rw [getD_coefficients_cons R a as j hj]
    cases j with
    | zero =>
      rw [ih 0 hj]
      simp [generatingPolynomial, add_mul, mul_assoc, Polynomial.coeff_add ]
    | succ j =>
      have hj' : j < R := Nat.lt_trans (Nat.lt_succ_self j) hj
      rw [ih (j + 1) hj]
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel, ih j hj']
      simp [generatingPolynomial, add_mul, mul_assoc, Polynomial.coeff_add,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]

/-- An instrumented execution of a coefficient pass, counting additions and
multiplications in S. -/
def measuredUpdate (a previous : S) : List S → List S × ℕ
  | [] => ([], 0)
  | b :: bs =>
    let next := measuredUpdate a b bs
    ((b + a * previous) :: next.1, next.2 + 2)

@[simp] theorem measuredUpdate_value (a previous : S) (bs : List S) :
    (measuredUpdate a previous bs).1 = update a previous bs := by
  induction bs generalizing previous with
  | nil => rfl
  | cons b bs ih => simp [measuredUpdate, update, ih]

@[simp] theorem measuredUpdate_operations (a previous : S) (bs : List S) :
    (measuredUpdate a previous bs).2 = 2 * bs.length := by
  induction bs generalizing previous with
  | nil => rfl
  | cons b bs ih => simp [measuredUpdate, ih, Nat.mul_succ]

/-- An instrumented execution of the entire retained-coefficient algorithm. -/
def measuredCoefficients (R : ℕ) : List S → List S × ℕ
  | [] => (initial R, 0)
  | a :: as =>
    let previous := measuredCoefficients R as
    let next := measuredUpdate a 0 previous.1
    (next.1, previous.2 + next.2)

@[simp] theorem measuredCoefficients_value (R : ℕ) (as : List S) :
    (measuredCoefficients R as).1 = coefficients R as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [measuredCoefficients, coefficients, ih]

/-- Exactly two semiring operations are executed for every input operator
and every retained coefficient. -/
theorem measuredCoefficients_operations (R : ℕ) (as : List S) :
    (measuredCoefficients R as).2 = 2 * R * as.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp [measuredCoefficients, ih, Nat.mul_succ]

end Recurrence

section SubsetSpecification

variable {ι S : Type*} [DecidableEq ι] [Semiring S]

/-- The order-independent product of a commuting family. This is used only
in the specification, never by the executable recurrence. -/
noncomputable def commutingProduct (f : ι → S)
    (hcomm : ∀ i j, Commute (f i) (f j)) (s : Finset ι) : S :=
  s.noncommProd f (fun _ _ _ _ _ => hcomm _ _)

/-- The mathematical elementary-symmetric sum over subsets of size j. -/
noncomputable def subsetCoefficient (f : ι → S)
    (hcomm : ∀ i j, Commute (f i) (f j)) (s : Finset ι) (j : ℕ) : S :=
  ∑ t ∈ s.powersetCard j, commutingProduct f hcomm t

omit [DecidableEq ι] in
@[simp] theorem commutingProduct_empty (f : ι → S)
    (hcomm : ∀ i j, Commute (f i) (f j)) :
    commutingProduct f hcomm ∅ = 1 := by
  unfold commutingProduct
  exact Finset.noncommProd_empty f _

theorem commutingProduct_insert (f : ι → S)
    (hcomm : ∀ i j, Commute (f i) (f j)) (s : Finset ι)
    (a : ι) (ha : a ∉ s) :
    commutingProduct f hcomm (insert a s) = f a * commutingProduct f hcomm s := by
  exact Finset.noncommProd_insert_of_notMem s a f _ ha

theorem commutingProduct_eq_list (f : ι → S)
    (hcomm : ∀ i j, Commute (f i) (f j)) (l : List ι) (hl : l.Nodup) :
    commutingProduct f hcomm l.toFinset = (l.map f).prod := by
  exact Finset.noncommProd_toFinset l f _ hl

theorem commutingProduct_eq_toList (f : ι → S)
    (hcomm : ∀ i j, Commute (f i) (f j)) (s : Finset ι) :
    commutingProduct f hcomm s = (s.toList.map f).prod := by
  simpa using commutingProduct_eq_list f hcomm s.toList s.nodup_toList

omit [DecidableEq ι] in
@[simp] theorem subsetCoefficient_zero (f : ι → S)
    (hcomm : ∀ i j, Commute (f i) (f j)) (s : Finset ι) :
    subsetCoefficient f hcomm s 0 = 1 := by
  simp [subsetCoefficient]

omit [DecidableEq ι] in
@[simp] theorem subsetCoefficient_empty (f : ι → S)
    (hcomm : ∀ i j, Commute (f i) (f j)) (j : ℕ) :
    subsetCoefficient f hcomm ∅ j = if j = 0 then 1 else 0 := by
  cases j with
  | zero => simp
  | succ j =>
    have he : (∅ : Finset ι).powersetCard (j + 1) = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by simp)
    simp [subsetCoefficient, he]

/-- Partitioning subsets according to whether they contain the newly
inserted index gives exactly the list-update recurrence. -/
theorem subsetCoefficient_insert_succ (f : ι → S)
    (hcomm : ∀ i j, Commute (f i) (f j)) (s : Finset ι)
    (a : ι) (ha : a ∉ s) (j : ℕ) :
    subsetCoefficient f hcomm (insert a s) (j + 1) =
      subsetCoefficient f hcomm s (j + 1) +
        f a * subsetCoefficient f hcomm s j := by
  have hdis : Disjoint (s.powersetCard (j + 1))
      ((s.powersetCard j).image (insert a)) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hv
    exact ha ((Finset.mem_powersetCard.mp hu).1 (Finset.mem_insert_self _ _))
  have hinj : ∀ u ∈ s.powersetCard j, ∀ v ∈ s.powersetCard j,
      insert a u = insert a v → u = v := by
    intro u hu v hv huv
    have hau : a ∉ u := fun h => ha ((Finset.mem_powersetCard.mp hu).1 h)
    have hav : a ∉ v := fun h => ha ((Finset.mem_powersetCard.mp hv).1 h)
    have he := congrArg (fun z : Finset ι => z.erase a) huv
    simpa [Finset.erase_insert, Finset.erase_eq_of_notMem hau,
      Finset.erase_eq_of_notMem hav] using he
  unfold subsetCoefficient
  rw [Finset.powersetCard_succ_insert ha, Finset.sum_union hdis,
    Finset.sum_image hinj, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  exact commutingProduct_insert f hcomm u a
    (fun h => ha ((Finset.mem_powersetCard.mp hu).1 h))

/-- For a duplicate-free list of indices, the executable recurrence equals
the genuine elementary-symmetric subset sum. Duplicate operator values are
allowed: only the indices must be distinct. -/
theorem coefficients_eq_subsetCoefficient (R : ℕ) (f : ι → S)
    (hcomm : ∀ i j, Commute (f i) (f j)) (l : List ι) (hl : l.Nodup)
    (j : ℕ) (hj : j < R) :
    (coefficients R (l.map f)).getD j 0 =
      subsetCoefficient f hcomm l.toFinset j := by
  induction l generalizing j with
  | nil =>
    simpa [coefficients] using getD_initial (S := S) R j hj
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hl
    have haf : a ∉ l.toFinset := by simpa using ha
    rw [List.map_cons, getD_coefficients_cons R (f a) (l.map f) j hj,
      List.toFinset_cons, ih hl j hj]
    cases j with
    | zero => simp
    | succ j =>
      have hj' : j < R := Nat.lt_trans (Nat.lt_succ_self j) hj
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel]
      rw [ih hl j hj']
      exact (subsetCoefficient_insert_succ f hcomm l.toFinset a haf j).symm

/-- The executable recurrence computes the exact ordered-list product
formula used for elementary operator polynomials in the layout. -/
theorem coefficients_eq_powersetCard (R : ℕ) (f : ι → S)
    (hcomm : ∀ i j, Commute (f i) (f j)) (l : List ι) (hl : l.Nodup)
    (j : ℕ) (hj : j < R) :
    (coefficients R (l.map f)).getD j 0 =
      ∑ t ∈ l.toFinset.powersetCard j, (t.toList.map f).prod := by
  rw [coefficients_eq_subsetCoefficient R f hcomm l hl j hj]
  unfold subsetCoefficient
  apply Finset.sum_congr rfl
  intro t _
  exact commutingProduct_eq_toList f hcomm t

end SubsetSpecification

section IndicatorInterpolation

variable {ι : Type*} [DecidableEq ι]

/-- On a zero-one family, the computed elementary coefficient is the
integer binomial coefficient in the number of ones, cast only afterwards. -/
theorem coefficients_indicator {S : Type*} [CommSemiring S]
    (R : ℕ) (l : List ι) (hl : l.Nodup) (ones : Finset ι)
    (hsub : ones ⊆ l.toFinset) (j : ℕ) (hj : j < R) :
    (coefficients R (l.map (fun i => if i ∈ ones then (1 : S) else 0))).getD j 0 =
      (ones.card.choose j : S) := by
  rw [coefficients_eq_subsetCoefficient R
    (fun i => if i ∈ ones then (1 : S) else 0)
    (fun _ _ => Commute.all _ _) l hl j hj]
  unfold subsetCoefficient commutingProduct
  simp only [Finset.noncommProd_eq_prod]
  exact BinomialInterpolation.sum_powersetCard_prod_indicator l.toFinset ones hsub j

/-- The computed coefficients, with the existing exact binomial
interpolation weights, yield corrected eigenvalue one on the entire
integer interval. No restriction on characteristic or R is imposed. -/
theorem parity_weighted_indicator {K : Type*} [CommRing K]
    (A R : ℕ) (l : List ι) (hl : l.Nodup) (ones : Finset ι)
    (hsub : ones ⊆ l.toFinset) (hA : A ≤ ones.card) (hR : ones.card < A + R) :
    (-1 : K) ^ ones.card *
      (∑ j ∈ Finset.range R,
        BinomialInterpolation.extendCoefficients
            (BinomialInterpolation.parityCoefficients (K := K) A R) j *
          (coefficients R (l.map (fun i => if i ∈ ones then (1 : K) else 0))).getD j 0)
        = 1 := by
  have hs :
      (∑ j ∈ Finset.range R,
        BinomialInterpolation.extendCoefficients
            (BinomialInterpolation.parityCoefficients (K := K) A R) j *
          (coefficients R (l.map (fun i => if i ∈ ones then (1 : K) else 0))).getD j 0) =
      ∑ j ∈ Finset.range R,
        BinomialInterpolation.extendCoefficients
            (BinomialInterpolation.parityCoefficients (K := K) A R) j *
          (ones.card.choose j : K) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [coefficients_indicator R l hl ones hsub j (Finset.mem_range.mp hj)]
  rw [hs, BinomialInterpolation.sum_range_extend_parity_of_mem A R ones.card hA hR,
    ← mul_pow]
  simp

end IndicatorInterpolation

end SubexponentialSAT.Subexp.Elementary

end OAI.Algorithms
