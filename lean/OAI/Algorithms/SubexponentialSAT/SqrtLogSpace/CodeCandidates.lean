import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationPayload
import OAI.Algorithms.SubexponentialSAT.SubexpTupleRefinement
import Mathlib.Tactic.NormNum.NatLog

/-! The retained domain of the code search is one word of two-bit scalars.
The tuple counter visits all four digits; the physical converter rejects the
unused digits and produces the original scalar-frame arithmetic format. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates

open SubexpEnumerationPayload

/-- The two bits are little endian, as in the supplied scalar encoding. -/
def digitBits (x : Bool × Bool) : List Bool := [x.1, x.2]

def tupleBits (xs : List (Bool × Bool)) : List Bool :=
  Encoding.encodeList digitBits xs

def scalarFrames (xs : List (Bool × Bool)) : List Bool :=
  xs.flatMap (Encoding.frame ∘ digitBits)

def invalidDigit (ternary : Bool) (x : Bool × Bool) : Bool :=
  if ternary then x.1 && x.2 else x.2

@[simp] theorem tupleBits_length (xs : List (Bool × Bool)) :
    (tupleBits xs).length = 6 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [tupleBits, Encoding.encodeList, digitBits] at *; omega

@[simp] theorem scalarFrames_length (xs : List (Bool × Bool)) :
    (scalarFrames xs).length = 5 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [scalarFrames, digitBits] at *; omega

/-- Physical counter words for a single field vector, never a family of vectors. -/
def fieldWords {p d : ℕ} [Fact p.Prime] (v : Fin d → ZMod p) : List (List Bool) :=
  List.ofFn fun i => scalarBits (v i)

@[simp] theorem fieldWords_shape {p d : ℕ} [Fact p.Prime] (v : Fin d → ZMod p) :
    (fieldWords v).map List.length = List.replicate d (scalarWidth p) := by
  simp [fieldWords, List.map_ofFn, Function.comp_def]

@[simp] theorem fieldWords_length {p d : ℕ} [Fact p.Prime] (v : Fin d → ZMod p) :
    (fieldWords v).length = d := by simp [fieldWords]

@[simp] theorem fieldWords_flatten_length {p d : ℕ} [Fact p.Prime]
    (v : Fin d → ZMod p) : (fieldWords v).flatten.length = d * scalarWidth p := by
  simp [List.length_flatten, fieldWords_shape]

theorem fieldWords_flatten {p d : ℕ} [Fact p.Prime] (v : Fin d → ZMod p) :
    (fieldWords v).flatten = SubexpTupleRefinement.encodeTuple (scalarCode p) v := by
  simpa [fieldWords, SubexpTupleRefinement.tuplePayload, scalarCode] using
    SubexpTupleRefinement.tuplePayload_map (scalarCode p) v

/-- Each field vector has one unique counter state. -/
theorem fieldWords_injective {p d : ℕ} [Fact p.Prime] :
    Function.Injective (fieldWords (p := p) (d := d)) := by
  intro v w h
  apply SubexpTupleRefinement.encodeTuple_injective (scalarCode p) d
  simpa only [fieldWords_flatten] using congrArg List.flatten h

/-- Rejecting binary digit 3 leaves precisely the original ternary alphabet. -/
theorem ternary_digit_sound (x : Bool × Bool) (hx : invalidDigit true x = false) :
    ∃ a : ZMod 3, digitBits x = scalarBits a := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b
  · exact ⟨0, by
      unfold scalarBits
      have hw : scalarWidth 3 = 2 := by norm_num [scalarWidth]
      rw [hw]
      decide⟩
  · exact ⟨2, by
      unfold scalarBits
      have hw : scalarWidth 3 = 2 := by norm_num [scalarWidth]
      rw [hw]
      decide⟩
  · exact ⟨1, by
      unfold scalarBits
      have hw : scalarWidth 3 = 2 := by norm_num [scalarWidth]
      rw [hw]
      decide⟩
  · simp [invalidDigit] at hx

/-- The binary graph search uses the same width-two scalar format. -/
theorem binary_digit_sound (x : Bool × Bool) (hx : invalidDigit false x = false) :
    ∃ a : ZMod 2, digitBits x = scalarBits a := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b
  · exact ⟨0, by
      unfold scalarBits
      have hw : scalarWidth 2 = 2 := by norm_num [scalarWidth]
      rw [hw]
      decide⟩
  · simp [invalidDigit] at hx
  · exact ⟨1, by
      unfold scalarBits
      have hw : scalarWidth 2 = 2 := by norm_num [scalarWidth]
      rw [hw]
      decide⟩
  · simp [invalidDigit] at hx


theorem ternary_digit_complete (x : Bool × Bool) (a : ZMod 3)
    (ha : digitBits x = scalarBits a) : invalidDigit true x = false := by
  have hw : scalarWidth 3 = 2 := by norm_num [scalarWidth]
  unfold scalarBits at ha
  rw [hw] at ha
  rcases x with ⟨b,c⟩
  cases b <;> cases c <;> simp [invalidDigit]
  all_goals
    simp [digitBits, SubexpLiftRing.fixedBits] at ha
    have hval := a.val_lt
    omega

theorem binary_digit_complete (x : Bool × Bool) (a : ZMod 2)
    (ha : digitBits x = scalarBits a) : invalidDigit false x = false := by
  have hw : scalarWidth 2 = 2 := by norm_num [scalarWidth]
  unfold scalarBits at ha
  rw [hw] at ha
  rcases x with ⟨b,c⟩
  cases b <;> cases c <;> simp [invalidDigit]
  all_goals
    simp [digitBits, SubexpLiftRing.fixedBits] at ha
    have hval := a.val_lt
    omega

/-- Invalid binary candidates and final overflow are charged: four to the
number of scalars is bounded by the square of the original ternary family. -/
theorem ternary_attempts_le_square (d : ℕ) : 2 ^ (2 * d) ≤ (3 ^ d) ^ 2 := by
  calc
    2 ^ (2 * d) = 4 ^ d := by rw [pow_mul]; norm_num
    _ ≤ 9 ^ d := Nat.pow_le_pow_left (by decide) d
    _ = (3 ^ d) ^ 2 := by rw [← pow_mul, Nat.mul_comm d 2, pow_mul]; norm_num


/-- Any width-two odometer state is exactly a list of scalar bit pairs. -/
theorem pairs_of_shape (words : List (List Bool)) (d : ℕ)
    (hshape : words.map List.length = List.replicate d 2) :
    ∃ xs : List (Bool × Bool), xs.length = d ∧ xs.map digitBits = words := by
  induction words generalizing d with
  | nil =>
    have hd : d = 0 := by simpa using congrArg List.length hshape.symm
    subst d
    exact ⟨[], rfl, rfl⟩
  | cons word words ih =>
    cases d with
    | zero => simp at hshape
    | succ d =>
      obtain ⟨hw, ht⟩ : word.length = 2 ∧ words.map List.length = List.replicate d 2 := by
        simpa [List.replicate_succ] using hshape
      obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hw
      obtain ⟨xs, hlen, hxs⟩ := ih d ht
      exact ⟨(a,b) :: xs, by simp [hlen], by simp [digitBits, hxs]⟩

private theorem digits_sound {p : ℕ} [Fact p.Prime] (xs : List (Bool × Bool))
    (h : ∀ x ∈ xs, ∃ a : ZMod p, digitBits x = scalarBits a) :
    ∃ v : Fin xs.length → ZMod p, xs.map digitBits = fieldWords v := by
  induction xs with
  | nil => exact ⟨Fin.elim0, rfl⟩
  | cons x xs ih =>
    obtain ⟨a, ha⟩ := h x (by simp)
    obtain ⟨v, hv⟩ := ih (fun y hy => h y (by simp [hy]))
    refine ⟨Fin.cons a v, ?_⟩
    simpa [fieldWords, List.ofFn_succ, ha] using congrArg (List.cons (scalarBits a)) hv

theorem ternary_digits_sound (xs : List (Bool × Bool))
    (hvalid : xs.any (invalidDigit true) = false) :
    ∃ v : Fin xs.length → ZMod 3, xs.map digitBits = fieldWords v := by
  apply digits_sound
  intro x hx
  apply ternary_digit_sound
  have h := List.any_eq_false.mp hvalid x hx
  exact Bool.eq_false_iff.mpr h

theorem binary_digits_sound (xs : List (Bool × Bool))
    (hvalid : xs.any (invalidDigit false) = false) :
    ∃ v : Fin xs.length → ZMod 2, xs.map digitBits = fieldWords v := by
  apply digits_sound
  intro x hx
  apply binary_digit_sound
  have h := List.any_eq_false.mp hvalid x hx
  exact Bool.eq_false_iff.mpr h


/-- Every actual ternary field vector passes the physical digit guard. -/
theorem ternary_field_valid (xs : List (Bool × Bool)) (v : Fin xs.length → ZMod 3)
    (h : xs.map digitBits = fieldWords v) : xs.any (invalidDigit true) = false := by
  apply List.any_eq_false.mpr
  intro x hx
  have hm : digitBits x ∈ fieldWords v := h ▸ List.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
  simp [ternary_digit_complete x (v i) hi.symm]

/-- The same assertion includes both scalar values of the graph alphabet. -/
theorem binary_field_valid (xs : List (Bool × Bool)) (v : Fin xs.length → ZMod 2)
    (h : xs.map digitBits = fieldWords v) : xs.any (invalidDigit false) = false := by
  apply List.any_eq_false.mpr
  intro x hx
  have hm : digitBits x ∈ fieldWords v := h ▸ List.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
  simp [binary_digit_complete x (v i) hi.symm]

theorem scalarFrames_eq_field_frames {p : ℕ} [Fact p.Prime]
    (xs : List (Bool × Bool)) (v : Fin xs.length → ZMod p)
    (h : xs.map digitBits = fieldWords v) :
    scalarFrames xs = (fieldWords v).flatMap Encoding.frame := by
  rw [← h, List.flatMap_map]
  rfl

/-- The streamed visit log covers every actual field word. The list in the
hypothesis is proof-only telemetry from the bounded-memory odometer. -/
theorem covers_field {R S : ℕ} {ports : ExecCNFTupleEnumeration.Ports R S}
    {body : StructuredCalls.Cmd R S} {p d steps : ℕ} [Fact p.Prime]
    {start finish : StructuredCalls.State R S}
    (visits : ExecCNFTupleEnumeration.Visits ports body
      (List.replicate d (scalarWidth p))
      (List.range' 0 (2 ^ (List.replicate d (scalarWidth p)).sum)) steps start finish)
    (v : Fin d → ZMod p) :
    ∃ a b nb, a.stacks ports.counter = Encoding.encodeList id (fieldWords v) ∧
      StructuredCalls.Eval body nb a b :=
  visits.covers (fieldWords v) (fieldWords_shape v)

/-- Row-major matrix indexing is the supplied `finProdFinEquiv` convention. -/
def matrixWords {p rows cols : ℕ} [Fact p.Prime]
    (matrix : Fin rows → Fin cols → ZMod p) : List (List Bool) :=
  fieldWords fun i : Fin (rows * cols) =>
    matrix (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

theorem matrixWords_of_vector {p rows cols : ℕ} [Fact p.Prime]
    (v : Fin (rows * cols) → ZMod p) :
    matrixWords (fun i j => v (finProdFinEquiv (i, j))) = fieldWords v := by
  unfold matrixWords
  congr 1
  funext i
  exact congrArg v (finProdFinEquiv.apply_symm_apply i)

/-- Every range-checked current matrix is an actual ternary matrix, with
the supplied row-major convention and including zero-sized dimensions. -/
theorem ternary_matrix_digits_sound (xs : List (Bool × Bool)) (rows cols : ℕ)
    (hlen : xs.length = rows * cols) (hvalid : xs.any (invalidDigit true) = false) :
    ∃ matrix : Fin rows → Fin cols → ZMod 3, xs.map digitBits = matrixWords matrix := by
  obtain ⟨v, hv⟩ := ternary_digits_sound xs hvalid
  let flat : Fin (rows * cols) → ZMod 3 := fun i => v (Fin.cast hlen.symm i)
  refine ⟨fun i j => flat (finProdFinEquiv (i,j)), ?_⟩
  rw [matrixWords_of_vector, hv]
  exact List.ofFn_congr hlen (fun i => scalarBits (v i))

theorem binary_matrix_digits_sound (xs : List (Bool × Bool)) (rows cols : ℕ)
    (hlen : xs.length = rows * cols) (hvalid : xs.any (invalidDigit false) = false) :
    ∃ matrix : Fin rows → Fin cols → ZMod 2, xs.map digitBits = matrixWords matrix := by
  obtain ⟨v, hv⟩ := binary_digits_sound xs hvalid
  let flat : Fin (rows * cols) → ZMod 2 := fun i => v (Fin.cast hlen.symm i)
  refine ⟨fun i j => flat (finProdFinEquiv (i,j)), ?_⟩
  rw [matrixWords_of_vector, hv]
  exact List.ofFn_congr hlen (fun i => scalarBits (v i))

@[simp] theorem matrixWords_shape {p rows cols : ℕ} [Fact p.Prime]
    (matrix : Fin rows → Fin cols → ZMod p) :
    (matrixWords matrix).map List.length = List.replicate (rows * cols) (scalarWidth p) :=
  fieldWords_shape _

theorem matrixWords_injective {p rows cols : ℕ} [Fact p.Prime] :
    Function.Injective (matrixWords (p := p) (rows := rows) (cols := cols)) := by
  intro a b hab
  have h := fieldWords_injective hab
  funext i j
  simpa only [Equiv.symm_apply_apply] using congrFun h (finProdFinEquiv (i,j))

/-- There is no exceptional matrix case when a dimension is zero. -/
theorem covers_matrix {R S : ℕ} {ports : ExecCNFTupleEnumeration.Ports R S}
    {body : StructuredCalls.Cmd R S} {p rows cols steps : ℕ} [Fact p.Prime]
    {start finish : StructuredCalls.State R S}
    (visits : ExecCNFTupleEnumeration.Visits ports body
      (List.replicate (rows * cols) (scalarWidth p))
      (List.range' 0 (2 ^ (List.replicate (rows * cols) (scalarWidth p)).sum))
      steps start finish)
    (matrix : Fin rows → Fin cols → ZMod p) :
    ∃ a b nb, a.stacks ports.counter = Encoding.encodeList id (matrixWords matrix) ∧
      StructuredCalls.Eval body nb a b :=
  visits.covers (matrixWords matrix) (matrixWords_shape matrix)

/-- Specification of one saved-candidate update. This is not an enumeration:
only the first accepted word is retained by the native selection command. -/
def saveFirst (accepted : ℕ → Bool) (encode : ℕ → List Bool)
    (saved : List Bool) (rank : ℕ) : List Bool :=
  if saved.isEmpty then if accepted rank then encode rank else [] else saved

theorem saveFirst_fold_of_saved (accepted : ℕ → Bool) (encode : ℕ → List Bool)
    (ranks : List ℕ) (saved : List Bool) (hsaved : saved ≠ []) :
    ranks.foldl (saveFirst accepted encode) saved = saved := by
  induction ranks with
  | nil => rfl
  | cons rank ranks ih => simpa [saveFirst, List.isEmpty_iff, hsaved] using ih

/-- The concrete loop's rank log specifies first success, not an arbitrary
successful witness. The log is not stored by the program. -/
theorem saveFirst_fold_eq_find (accepted : ℕ → Bool) (encode : ℕ → List Bool)
    (ranks : List ℕ) (hnonempty : ∀ rank, encode rank ≠ []) :
    ranks.foldl (saveFirst accepted encode) [] =
      ((ranks.find? accepted).map encode).getD [] := by
  induction ranks with
  | nil => rfl
  | cons rank ranks ih =>
    cases ha : accepted rank with
    | false => simpa [saveFirst, ha] using ih
    | true =>
      simpa [saveFirst, ha] using
        saveFirst_fold_of_saved accepted encode ranks (encode rank) (hnonempty rank)

/-- Coverage of one successful rank forces the physical saved-word fold to
contain a successful candidate. The rank log is proof evidence only. -/
theorem saveFirst_fold_success (accepted : ℕ → Bool) (encode : ℕ → List Bool)
    (ranks : List ℕ) (hnonempty : ∀ rank, encode rank ≠ [])
    (hexists : ∃ rank ∈ ranks, accepted rank = true) :
    ∃ rank ∈ ranks, accepted rank = true ∧
      ranks.foldl (saveFirst accepted encode) [] = encode rank := by
  have hsome : (ranks.find? accepted).isSome := List.find?_isSome.mpr hexists
  cases hfind : ranks.find? accepted with
  | none => simp [hfind] at hsome
  | some rank =>
      refine ⟨rank, List.mem_of_find?_eq_some hfind, List.find?_some hfind, ?_⟩
      rw [saveFirst_fold_eq_find accepted encode ranks hnonempty, hfind]
      rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates
