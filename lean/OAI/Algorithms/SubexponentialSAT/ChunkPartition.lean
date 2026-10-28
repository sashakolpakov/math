import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# An explicit ceiling-based partition into Boolean chunks

For positive `ell`, the number of chunks is `(n + ell - 1) / ell`.
The `i`th chunk contains the consecutive indices starting at `i * ell` and
has size `min ell (n - i * ell)`. Quotient and remainder give an actual
equivalence between the original indices and chunk/offset pairs.
-/

namespace SubexponentialSAT.ChunkPartition

open scoped BigOperators

/-- The natural-number ceiling of `n / ell` for positive `ell`. -/
def count (n ell : ℕ) : ℕ := (n + ell - 1) / ell

/-- Size of each consecutive chunk, allowing a shorter final chunk. -/
def size (n ell : ℕ) (i : Fin (count n ell)) : ℕ :=
  min ell (n - i.val * ell)

/-- Chunk index together with a valid within-chunk offset. -/
abbrev Index (n ell : ℕ) := Σ i : Fin (count n ell), Fin (size n ell i)

theorem count_le_iff {n ell d : ℕ} (hell : 0 < ell) :
    count n ell ≤ d ↔ n ≤ d * ell := by
  unfold count
  rw [Nat.div_le_iff_le_mul hell]
  omega

theorem lt_count_iff {n ell i : ℕ} (hell : 0 < ell) :
    i < count n ell ↔ i * ell < n := by
  have h := count_le_iff (n := n) (ell := ell) (d := i) hell
  omega

theorem le_count_mul {n ell : ℕ} (hell : 0 < ell) :
    n ≤ count n ell * ell :=
  (count_le_iff hell).mp le_rfl

@[simp] theorem count_zero {ell : ℕ} (hell : 0 < ell) : count 0 ell = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (count_le_iff hell).mpr (by simp)

@[simp] theorem count_eq_zero_iff {n ell : ℕ} (hell : 0 < ell) :
    count n ell = 0 ↔ n = 0 := by
  constructor
  · intro h
    have hn := le_count_mul (n := n) hell
    simp [h] at hn
    exact hn
  · rintro rfl
    exact count_zero hell

theorem count_pos_iff {n ell : ℕ} (hell : 0 < ell) :
    0 < count n ell ↔ 0 < n := by
  have h := count_eq_zero_iff (n := n) hell
  omega

theorem count_le_div_add_one {n ell : ℕ} (hell : 0 < ell) :
    count n ell ≤ n / ell + 1 := by
  apply (count_le_iff hell).mpr
  have hr := Nat.mod_lt n hell
  have heq := Nat.div_add_mod' n ell
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem count_eq_div_add_ite {n ell : ℕ} (hell : 0 < ell) :
    count n ell = n / ell + if n % ell = 0 then 0 else 1 := by
  have hdiv := Nat.div_add_mod' n ell
  by_cases hr : n % ell = 0
  · simp only [hr, ite_true, Nat.add_zero]
    apply Nat.le_antisymm
    · apply (count_le_iff hell).mpr
      omega
    · have h := Nat.div_le_div_right (c := ell) (le_count_mul (n := n) hell)
      simpa only [Nat.mul_div_cancel _ hell] using h
  · simp only [hr, ite_false]
    apply Nat.le_antisymm (count_le_div_add_one hell)
    have hlt : n / ell < count n ell := (lt_count_iff hell).mpr (by omega)
    omega

theorem size_le (n ell : ℕ) (i : Fin (count n ell)) : size n ell i ≤ ell :=
  Nat.min_le_left _ _

theorem chunk_start_lt {n ell : ℕ} (hell : 0 < ell) (i : Fin (count n ell)) :
    i.val * ell < n := (lt_count_iff hell).mp i.isLt

theorem size_pos {n ell : ℕ} (hell : 0 < ell) (i : Fin (count n ell)) :
    0 < size n ell i := by
  have hi := chunk_start_lt hell i
  unfold size
  omega

theorem size_eq_ell_of_end_le {n ell : ℕ} (i : Fin (count n ell))
    (hend : (i.val + 1) * ell ≤ n) : size n ell i = ell := by
  rw [Nat.add_mul, Nat.one_mul] at hend
  apply Nat.min_eq_left
  omega

/-- Every chunk before the last has the full prescribed size. -/
theorem size_eq_ell_of_not_last {n ell : ℕ} (hell : 0 < ell)
    (i : Fin (count n ell)) (hi : i.val + 1 < count n ell) :
    size n ell i = ell :=
  size_eq_ell_of_end_le i ((lt_count_iff hell).mp hi).le

/-- The actual final chunk exists precisely when the input has a variable. -/
def lastIndex (n ell : ℕ) (hell : 0 < ell) (hn : 0 < n) : Fin (count n ell) :=
  ⟨count n ell - 1, by
    have h := (count_pos_iff hell).mpr hn
    omega⟩

theorem last_size_eq_remaining {n ell : ℕ} (hell : 0 < ell) (hn : 0 < n) :
    size n ell (lastIndex n ell hell hn) = n - (count n ell - 1) * ell := by
  have hD : 0 < count n ell := (count_pos_iff hell).mpr hn
  have hcount : count n ell = (count n ell - 1) + 1 := by omega
  have hbound := le_count_mul (n := n) hell
  conv_rhs at hbound => rw [hcount]
  rw [Nat.add_mul, Nat.one_mul] at hbound
  change min ell (n - (count n ell - 1) * ell) = _
  apply Nat.min_eq_right
  omega

/-- A divisible input has a full last chunk; otherwise the last chunk has
exactly the positive remainder. No empty trailing chunk is introduced. -/
theorem last_size_eq_remainder {n ell : ℕ} (hell : 0 < ell) (hn : 0 < n) :
    size n ell (lastIndex n ell hell hn) =
      if n % ell = 0 then ell else n % ell := by
  rw [last_size_eq_remaining hell hn]
  have hdiv := Nat.div_add_mod' n ell
  by_cases hr : n % ell = 0
  · simp only [hr, ite_true]
    have hcount : count n ell = n / ell := by
      simpa only [hr, ite_true, Nat.add_zero] using count_eq_div_add_ite (n := n) hell
    have hq : 0 < n / ell := by
      have hD := (count_pos_iff hell).mpr hn
      omega
    have hqeq : n / ell = (n / ell - 1) + 1 := by omega
    have hmul : n / ell * ell = (n / ell - 1) * ell + ell := by
      conv_lhs => rw [hqeq]
      rw [Nat.add_mul, Nat.one_mul]
    rw [hcount]
    omega
  · simp only [hr, ite_false]
    have hcount : count n ell = n / ell + 1 := by
      simpa only [hr, ite_false] using count_eq_div_add_ite (n := n) hell
    rw [hcount]
    simp only [Nat.add_sub_cancel]
    omega

theorem quotient_lt_count {n ell x : ℕ} (hell : 0 < ell) (hx : x < n) :
    x / ell < count n ell := by
  apply (lt_count_iff hell).mpr
  exact lt_of_le_of_lt (Nat.div_mul_le_self x ell) hx

/-- Split an original index into quotient and remainder. -/
def splitIndex (n ell : ℕ) (hell : 0 < ell) (x : Fin n) : Index n ell :=
  ⟨⟨x.val / ell, quotient_lt_count hell x.isLt⟩,
    ⟨x.val % ell, by
      change x.val % ell < min ell (n - x.val / ell * ell)
      have hr := Nat.mod_lt x.val hell
      have heq := Nat.div_add_mod' x.val ell
      have hx := x.isLt
      omega⟩⟩

/-- Reassemble a chunk/offset pair as an original index. -/
def joinIndex (n ell : ℕ) (hell : 0 < ell) (s : Index n ell) : Fin n :=
  ⟨s.1.val * ell + s.2.val, by
    have hs := s.2.isLt
    change s.2.val < min ell (n - s.1.val * ell) at hs
    have hi := chunk_start_lt hell s.1
    omega⟩

@[simp] theorem join_split (n ell : ℕ) (hell : 0 < ell) (x : Fin n) :
    joinIndex n ell hell (splitIndex n ell hell x) = x := by
  apply Fin.ext
  exact Nat.div_add_mod' x.val ell

@[simp] theorem split_join (n ell : ℕ) (hell : 0 < ell) (s : Index n ell) :
    splitIndex n ell hell (joinIndex n ell hell s) = s := by
  have hoff : s.2.val < ell := lt_of_lt_of_le s.2.isLt (size_le n ell s.1)
  have hd : (s.1.val * ell + s.2.val) / ell = s.1.val := by
    rw [Nat.mul_comm s.1.val ell, Nat.mul_add_div hell, Nat.div_eq_of_lt hoff]
    simp
  have hm : (s.1.val * ell + s.2.val) % ell = s.2.val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hoff]
  have hi : (splitIndex n ell hell (joinIndex n ell hell s)).1 = s.1 :=
    Fin.ext hd
  apply Sigma.ext hi
  apply (Fin.heq_ext_iff (congrArg (size n ell) hi)).mpr
  exact hm

/-- The concrete partition equivalence required by Boolean packing. -/
def indexEquiv (n ell : ℕ) (hell : 0 < ell) : Fin n ≃ Index n ell where
  toFun := splitIndex n ell hell
  invFun := joinIndex n ell hell
  left_inv := join_split n ell hell
  right_inv := split_join n ell hell

@[simp] theorem indexEquiv_chunk_val (n ell : ℕ) (hell : 0 < ell) (x : Fin n) :
    (indexEquiv n ell hell x).1.val = x.val / ell := rfl

@[simp] theorem indexEquiv_offset_val (n ell : ℕ) (hell : 0 < ell) (x : Fin n) :
    (indexEquiv n ell hell x).2.val = x.val % ell := rfl

@[simp] theorem indexEquiv_symm_val (n ell : ℕ) (hell : 0 < ell) (s : Index n ell) :
    ((indexEquiv n ell hell).symm s).val = s.1.val * ell + s.2.val := rfl

/-- The chunk sizes sum to exactly the original number of variables. -/
theorem sum_size (n ell : ℕ) (hell : 0 < ell) :
    (∑ i : Fin (count n ell), size n ell i) = n := by
  have h := Fintype.card_congr (indexEquiv n ell hell)
  simpa only [Fintype.card_fin, Fintype.card_sigma] using h.symm

end SubexponentialSAT.ChunkPartition

end OAI.Algorithms
