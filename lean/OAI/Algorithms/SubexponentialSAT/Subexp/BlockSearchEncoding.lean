import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearch

namespace OAI.Algorithms

/-!
# Coordinate-major representation of a complete local basis table

The encoded search enumerates one square table and a split position.  Rows
are ambient coordinates and columns are basis vectors.  This module proves
that this representation covers every successful kernel/complement pair.
No transpose or basis search is performed by these definitions.
-/

namespace SubexponentialSAT.Subexp.BlockSearchEncoding

open BlockSearch
open scoped BigOperators

variable {K : Type*} {N : ℕ}

/-- View a flat coordinate-major vector as a square table. -/
def unflattenTable (x : Fin (N * N) → K) (row col : Fin N) : K :=
  x (finProdFinEquiv (row, col))

/-- Read the entries of a square table in coordinate-major order. -/
def flattenTable (T : Fin N → Fin N → K) (i : Fin (N * N)) : K :=
  T (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

@[simp] theorem unflattenTable_flattenTable (T : Fin N → Fin N → K) :
    unflattenTable (flattenTable T) = T := by
  funext row col
  simp [unflattenTable, flattenTable]

@[simp] theorem flattenTable_unflattenTable (x : Fin (N * N) → K) :
    flattenTable (unflattenTable x) = x := by
  funext i
  change x (finProdFinEquiv (finProdFinEquiv.symm i)) = x i
  rw [Equiv.apply_symm_apply]

@[simp] theorem flattenTable_product (T : Fin N → Fin N → K) (row col : Fin N) :
    flattenTable T (finProdFinEquiv (row, col)) = T row col := by
  simp [flattenTable]

/-- An executable bijection; it uses quotient/remainder indexing only. -/
def flatTableEquiv : (Fin (N * N) → K) ≃ (Fin N → Fin N → K) where
  toFun := unflattenTable
  invFun := flattenTable
  left_inv := flattenTable_unflattenTable
  right_inv := unflattenTable_flattenTable

/-- Coordinate-major rows, directly consumable by a matrix/vector scan. -/
def tableRows (T : Fin N → Fin N → K) : List (List K) :=
  List.ofFn fun row => List.ofFn (T row)

/-- Coordinate-major flat entries. -/
def tableEntries (T : Fin N → Fin N → K) : List K :=
  List.ofFn (flattenTable T)

@[simp] theorem tableRows_length (T : Fin N → Fin N → K) :
    (tableRows T).length = N := by simp [tableRows]

theorem tableRows_row_length (T : Fin N → Fin N → K) (row : List K)
    (hrow : row ∈ tableRows T) : row.length = N := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
  simp

@[simp] theorem tableEntries_length (T : Fin N → Fin N → K) :
    (tableEntries T).length = N * N := by simp [tableEntries]

/-- The flat index order is exactly the matrix scan's row concatenation. -/
theorem tableEntries_eq_flatten_rows (T : Fin N → Fin N → K) :
    tableEntries T = (tableRows T).flatten := by
  rw [tableEntries, List.ofFn_mul]
  unfold tableRows
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext row
  apply congrArg List.ofFn
  funext col
  have hi : (⟨row.val * N + col.val, by
      simpa [Nat.mul_comm, Nat.add_comm] using (finProdFinEquiv (row, col)).isLt⟩ : Fin (N * N)) =
      finProdFinEquiv (row, col) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [hi]
  exact flattenTable_product T row col

/-- Split a square coordinate-major table into its first `d` columns and
its remaining columns. -/
def splitPair (d : Fin (N + 1)) (T : Fin N → Fin N → K) :
    Candidate K N × Candidate K N :=
  (⟨d, fun i row => T row ⟨i.val, by have := d.isLt; omega⟩⟩,
   ⟨⟨N - d.val, Nat.lt_succ_of_le (Nat.sub_le N d.val)⟩,
    fun j row => T row ⟨d.val + j.val, by
      have hj : j.val < N - d.val := j.isLt
      have hd := d.isLt
      omega⟩⟩)

@[simp] theorem splitPair_first_dimension (d : Fin (N + 1))
    (T : Fin N → Fin N → K) : (splitPair d T).1.1 = d := rfl

@[simp] theorem splitPair_second_dimension (d : Fin (N + 1))
    (T : Fin N → Fin N → K) : (splitPair d T).2.1.val = N - d.val := rfl

theorem splitPair_dimensions_add (d : Fin (N + 1)) (T : Fin N → Fin N → K) :
    (splitPair d T).1.1.val + (splitPair d T).2.1.val = N := by
  simp only [splitPair_first_dimension, splitPair_second_dimension]
  have := d.isLt
  omega

@[simp] theorem splitPair_first_apply (d : Fin (N + 1))
    (T : Fin N → Fin N → K) (i : Fin d.val) (row : Fin N) :
    (splitPair d T).1.2 i row = T row ⟨i.val, by have := d.isLt; omega⟩ := rfl

@[simp] theorem splitPair_second_apply (d : Fin (N + 1))
    (T : Fin N → Fin N → K) (j : Fin (N - d.val)) (row : Fin N) :
    (splitPair d T).2.2 j row = T row ⟨d.val + j.val, by have := j.isLt; omega⟩ := rfl

/-- Read a successful pair as one coordinate-major square table. The
dimension equality is used only to certify the second column index. -/
def tableOfPair (c : Candidate K N × Candidate K N)
    (h : c.1.1.val + c.2.1.val = N) (row col : Fin N) : K :=
  if hc : col.val < c.1.1.val then c.1.2 ⟨col.val, hc⟩ row
  else c.2.2 ⟨col.val - c.1.1.val, by have := col.isLt; omega⟩ row

@[simp] theorem tableOfPair_first (c : Candidate K N × Candidate K N)
    (h : c.1.1.val + c.2.1.val = N) (i : Fin c.1.1.val) (row : Fin N) :
    tableOfPair c h row ⟨i.val, by have := i.isLt; omega⟩ = c.1.2 i row := by
  simp [tableOfPair, i.isLt]

@[simp] theorem tableOfPair_second (c : Candidate K N × Candidate K N)
    (h : c.1.1.val + c.2.1.val = N) (j : Fin c.2.1.val) (row : Fin N) :
    tableOfPair c h row ⟨c.1.1.val + j.val, by have := j.isLt; omega⟩ =
      c.2.2 j row := by
  simp [tableOfPair]

/-- Joining a split table returns exactly its original entries. -/
@[simp] theorem tableOfPair_splitPair (d : Fin (N + 1))
    (T : Fin N → Fin N → K) :
    tableOfPair (splitPair d T) (splitPair_dimensions_add d T) = T := by
  funext row col
  by_cases h : col.val < d.val
  · simp [tableOfPair, splitPair, h]
  · simp [tableOfPair, splitPair, h, Nat.add_sub_of_le (Nat.le_of_not_gt h)]

/-- Splitting the table of a pair with the full ambient dimension returns
the exact pair, including its dependent dimension indices. -/
@[simp] theorem splitPair_tableOfPair (c : Candidate K N × Candidate K N)
    (h : c.1.1.val + c.2.1.val = N) :
    splitPair c.1.1 (tableOfPair c h) = c := by
  rcases c with ⟨⟨d, v⟩, ⟨e, w⟩⟩
  have he : e = ⟨N - d.val, Nat.lt_succ_of_le (Nat.sub_le N d.val)⟩ := by
    apply Fin.ext
    change e.val = N - d.val
    change d.val + e.val = N at h
    omega
  subst e
  apply Prod.ext
  · apply congrArg (fun f : Fin d.val → Vec K N => (⟨d, f⟩ : Candidate K N))
    funext i row
    simp [ tableOfPair, i.isLt]
  · apply congrArg (fun f : Fin (N - d.val) → Vec K N =>
      (⟨⟨N - d.val, Nat.lt_succ_of_le (Nat.sub_le N d.val)⟩, f⟩ : Candidate K N))
    funext j row
    simp [ tableOfPair]

/-- Restrict a full coefficient vector to the first group of columns. -/
def headCoefficients (d : Fin (N + 1)) (x : Fin N → K) : Fin d.val → K :=
  fun i => x ⟨i.val, by have := d.isLt; omega⟩

/-- Restrict a full coefficient vector to the remaining columns. -/
def tailCoefficients (d : Fin (N + 1)) (x : Fin N → K) : Fin (N - d.val) → K :=
  fun j => x ⟨d.val + j.val, by have := j.isLt; omega⟩

theorem sum_split {A : Type*} [AddCommMonoid A] (d : Fin (N + 1)) (f : Fin N → A) :
    (∑ i, f i) =
      (∑ i : Fin d.val, f ⟨i.val, by have := d.isLt; omega⟩) +
      ∑ j : Fin (N - d.val), f ⟨d.val + j.val, by have := j.isLt; omega⟩ := by
  have hN : d.val + (N - d.val) = N := by have := d.isLt; omega
  let e : Fin d.val ⊕ Fin (N - d.val) ≃ Fin N :=
    finSumFinEquiv.trans (finCongr hN)
  have he₁ (i : Fin d.val) : e (.inl i) = ⟨i.val, by have := d.isLt; omega⟩ := by
    apply Fin.ext
    simp [e]
  have he₂ (j : Fin (N - d.val)) :
      e (.inr j) = ⟨d.val + j.val, by have := j.isLt; omega⟩ := by
    apply Fin.ext
    simp [e]
  calc
    (∑ i, f i) = ∑ j, f (e j) := (e.sum_comp f).symm
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp only [he₁, he₂]

/-- Join coefficient vectors in the same column order used by `splitPair`. -/
def joinCoefficients (d : Fin (N + 1)) (a : Fin d.val → K)
    (b : Fin (N - d.val) → K) (i : Fin N) : K :=
  if hi : i.val < d.val then a ⟨i.val, hi⟩
  else b ⟨i.val - d.val, by have := i.isLt; have := d.isLt; omega⟩

@[simp] theorem headCoefficients_join (d : Fin (N + 1))
    (a : Fin d.val → K) (b : Fin (N - d.val) → K) :
    headCoefficients d (joinCoefficients d a b) = a := by
  funext i
  simp [headCoefficients, joinCoefficients, i.isLt]

@[simp] theorem tailCoefficients_join (d : Fin (N + 1))
    (a : Fin d.val → K) (b : Fin (N - d.val) → K) :
    tailCoefficients d (joinCoefficients d a b) = b := by
  funext j
  simp [tailCoefficients, joinCoefficients]

@[simp] theorem joinCoefficients_restrictions (d : Fin (N + 1)) (x : Fin N → K) :
    joinCoefficients d (headCoefficients d x) (tailCoefficients d x) = x := by
  funext i
  by_cases hi : i.val < d.val
  · simp [joinCoefficients, headCoefficients, hi]
  · simp [joinCoefficients, tailCoefficients, hi, Nat.add_sub_of_le (Nat.le_of_not_gt hi)]

/-- Full coefficients are equivalent to the two restrictions. -/
def coefficientEquiv (d : Fin (N + 1)) :
    (Fin N → K) ≃ ((Fin d.val → K) × (Fin (N - d.val) → K)) where
  toFun x := (headCoefficients d x, tailCoefficients d x)
  invFun ab := joinCoefficients d ab.1 ab.2
  left_inv := joinCoefficients_restrictions d
  right_inv ab := by simp

theorem coefficients_zero_iff [Zero K] (d : Fin (N + 1)) (x : Fin N → K) :
    (headCoefficients d x = 0 ∧ tailCoefficients d x = 0) ↔ x = 0 := by
  constructor
  · rintro ⟨ha, hb⟩
    have h := joinCoefficients_restrictions d x
    rw [ha, hb] at h
    have hz : joinCoefficients d (0 : Fin d.val → K) (0 : Fin (N - d.val) → K) = 0 := by
      funext i
      simp [joinCoefficients]
    exact h.symm.trans hz
  · rintro rfl
    exact ⟨rfl, rfl⟩

section Field

variable [Field K] [DecidableEq K]

omit [DecidableEq K] in
/-- Multiplication of the coordinate-major table is exactly the sum of the
kernel-tuple and complement-tuple linear combinations. -/
theorem matrixMap_eq_combine (d : Fin (N + 1)) (T : Fin N → Fin N → K)
    (x : Fin N → K) :
    matrixMap T x =
      combine (splitPair d T).1 (headCoefficients d x) +
      combine (splitPair d T).2 (tailCoefficients d x) := by
  ext row
  rw [show matrixMap T x row = ∑ j : Fin N, T row j * x j from rfl]
  simp only [Pi.add_apply, combine, Finset.sum_apply, Pi.smul_apply,
    headCoefficients, tailCoefficients, smul_eq_mul]
  rw [sum_split d (fun i => T row i * x i)]
  congr 1 <;>
    apply Finset.sum_congr rfl <;>
    intro i _ <;>
    rw [mul_comm] <;>
    rfl

omit [DecidableEq K] in
/-- Correct kernel and complement data necessarily contain exactly `N`
basis vectors in total. -/
theorem dimensions_add {m : ℕ} {M : Fin m → Fin N → K}
    {c : Candidate K N × Candidate K N} (hc : GoodPair M c) :
    c.1.1.val + c.2.1.val = N := by
  have h := Submodule.finrank_add_eq_of_isCompl hc.isCompl
  rw [hc.1.finrank_kernel, hc.finrank_complement, Module.finrank_pi,
    Fintype.card_fin] at h
  exact h

omit [DecidableEq K] in
/-- The square-table search space covers every valid pair, independently
  of the order used to enumerate tables or split positions. -/
theorem goodPair_is_splitPair {m : ℕ} {M : Fin m → Fin N → K}
    {c : Candidate K N × Candidate K N} (hc : GoodPair M c) :
    ∃ (d : Fin (N + 1)) (T : Fin N → Fin N → K), splitPair d T = c :=
  ⟨c.1.1, tableOfPair c (dimensions_add hc), splitPair_tableOfPair c _⟩

omit [DecidableEq K] in
/-- Enumerating flat vectors of length `N²` and split positions covers every
valid pair; no separately prepared matrix representation is assumed. -/
theorem goodPair_is_flat_splitPair {m : ℕ} {M : Fin m → Fin N → K}
    {c : Candidate K N × Candidate K N} (hc : GoodPair M c) :
    ∃ (d : Fin (N + 1)) (x : Fin (N * N) → K),
      splitPair d (unflattenTable x) = c := by
  obtain ⟨d, T, hT⟩ := goodPair_is_splitPair hc
  refine ⟨d, flattenTable T, ?_⟩
  simpa using hT

omit [DecidableEq K] in
/-- At least one square table and split passes the actual pair specification. -/
theorem exists_good_splitPair {m : ℕ} (M : Fin m → Fin N → K) :
    ∃ (d : Fin (N + 1)) (T : Fin N → Fin N → K), GoodPair M (splitPair d T) := by
  obtain ⟨c, hc⟩ := exists_goodPair M
  obtain ⟨d, T, hT⟩ := goodPair_is_splitPair hc
  exact ⟨d, T, hT.symm ▸ hc⟩

end Field

end SubexponentialSAT.Subexp.BlockSearchEncoding

end OAI.Algorithms
