import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BooleanPacking

namespace OAI.Algorithms

/-!
# Fixed-width binary encodings of finite stack alphabets

The primary representation has no appended binary sentinel: the tape alphabet
is `Option Bool`, data bits are wrapped in `some`, and `none` is blank. Thus a
Boolean input stack can use width one and needs no initialization scan.

An explicit binary bottom-marker representation is also provided separately.
No theorem in this file assigns a Turing-machine cost to list operations.
-/

namespace SubexponentialSAT.StackEncoding

universe u

/-- An injective, positive, fixed-width code. -/
structure BlockCode (α : Type u) where
  width : ℕ
  width_pos : 0 < width
  block : α → List Bool
  length_block : ∀ a, (block a).length = width
  injective_block : Function.Injective block

/-- A positive width sufficient for every label in `Fin n`, including `n = 0`. -/
def codingWidth (n : ℕ) : ℕ := Nat.log 2 n + 1

theorem codingWidth_pos (n : ℕ) : 0 < codingWidth n := Nat.zero_lt_succ _

theorem codingWidth_capacity (n : ℕ) : n ≤ 2 ^ codingWidth n :=
  Nat.le_of_lt (Nat.lt_pow_succ_log_self Nat.one_lt_two n)

/-- Code construction from an explicitly supplied finite enumeration. -/
def codeOfEquiv {α : Type u} {n : ℕ} (e : α ≃ Fin n) : BlockCode α where
  width := codingWidth n
  width_pos := codingWidth_pos n
  block a := List.ofFn ((BooleanPacking.chunkEquiv (codingWidth n)).symm
    ⟨(e a).val, lt_of_lt_of_le (e a).isLt (codingWidth_capacity n)⟩)
  length_block _ := List.length_ofFn
  injective_block := by
    intro a b hab
    have hfun := List.ofFn_injective hab
    have hlabel := (BooleanPacking.chunkEquiv (codingWidth n)).symm.injective hfun
    apply e.injective
    exact Fin.ext (congrArg (fun x : Fin (2 ^ codingWidth n) => x.val) hlabel)

/-- Read exactly `w` bits, using a default only outside the supplied word. -/
def chunkOfList (w : ℕ) (bits : List Bool) : BooleanPacking.Chunk w :=
  fun i => (bits[i.val]?).getD false

@[simp] theorem chunkOfList_ofFn {w : ℕ} (x : BooleanPacking.Chunk w) :
    chunkOfList w (List.ofFn x) = x := by
  funext i
  simp [chunkOfList, i.isLt]

/-- A concrete decoder: check the width, decode the binary integer, then check
that it is a label in the finite alphabet. All checks are bounded. -/
def readCodeOfEquiv {α : Type u} {n : ℕ} (e : α ≃ Fin n) (bits : List Bool) : Option α :=
  if bits.length = codingWidth n then
    let label := BooleanPacking.chunkEquiv (codingWidth n) (chunkOfList (codingWidth n) bits)
    if h : label.val < n then some (e.symm ⟨label.val, h⟩) else none
  else none

@[simp] theorem readCodeOfEquiv_block {α : Type u} {n : ℕ} (e : α ≃ Fin n) (a : α) :
    readCodeOfEquiv e ((codeOfEquiv e).block a) = some a := by
  simp only [readCodeOfEquiv, codeOfEquiv, List.length_ofFn,
    chunkOfList_ofFn, Equiv.apply_symm_apply, Fin.val_mk, dite_eq_left (e a).isLt]
  exact congrArg some (e.symm_apply_apply a)

@[simp] theorem readCodeOfEquiv_nil {α : Type u} {n : ℕ} (e : α ≃ Fin n) :
    readCodeOfEquiv e [] = none := by
  have h : (0 : ℕ) ≠ codingWidth n := Nat.ne_of_lt (codingWidth_pos n)
  simp [readCodeOfEquiv, h]

/-- Any finite alphabet admits such a code. The chosen enumeration is fixed
data; the actual constructor `codeOfEquiv` is computable from that data. -/
noncomputable def finiteCode (α : Type u) [Fintype α] : BlockCode α :=
  codeOfEquiv (Fintype.equivFin α)

/-- A width-one code for an alphabet explicitly equivalent to Boolean bits. -/
def codeOfBoolEquiv {α : Type u} (e : α ≃ Bool) : BlockCode α where
  width := 1
  width_pos := Nat.zero_lt_succ 0
  block a := [e a]
  length_block _ := rfl
  injective_block := by
    intro a b hab
    exact e.injective (by simpa using hab)

/-- Raw Boolean input is already encoded and needs no setup pass. -/
def boolCode : BlockCode Bool := codeOfBoolEquiv (Equiv.refl Bool)

theorem take_block_append {α : Type u} (c : BlockCode α) (a : α) (rest : List Bool) :
    (c.block a ++ rest).take c.width = c.block a :=
  List.take_left' (c.length_block a)

theorem drop_block_append {α : Type u} (c : BlockCode α) (a : α) (rest : List Bool) :
    (c.block a ++ rest).drop c.width = rest :=
  List.drop_left' (c.length_block a)

/-- Top-at-head concatenation of symbol blocks, with blank as the external
end marker. -/
def encodeDataStack {α : Type u} (c : BlockCode α) : List α → List Bool
  | [] => []
  | a :: s => c.block a ++ encodeDataStack c s

abbrev encodeBlocks {α : Type u} := @encodeDataStack α

@[simp] theorem encodeDataStack_nil {α : Type u} (c : BlockCode α) :
    encodeDataStack c [] = [] := rfl

@[simp] theorem encodeDataStack_cons {α : Type u} (c : BlockCode α) (a : α)
    (s : List α) : encodeDataStack c (a :: s) = c.block a ++ encodeDataStack c s := rfl

theorem encodeDataStack_eq_flatMap {α : Type u} (c : BlockCode α) (s : List α) :
    encodeDataStack c s = s.flatMap c.block := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [encodeDataStack, ih]

@[simp] theorem encodeDataStack_append {α : Type u} (c : BlockCode α)
    (s t : List α) :
    encodeDataStack c (s ++ t) = encodeDataStack c s ++ encodeDataStack c t := by
  induction s with
  | nil => simp
  | cons a s ih => simp [ih, List.append_assoc]

@[simp] theorem length_encodeDataStack {α : Type u} (c : BlockCode α) (s : List α) :
    (encodeDataStack c s).length = s.length * c.width := by
  induction s with
  | nil => simp
  | cons a s ih => simp [c.length_block, ih, Nat.add_mul, Nat.add_comm]

@[simp] theorem take_width_cons {α : Type u} (c : BlockCode α) (a : α) (s : List α) :
    (encodeDataStack c (a :: s)).take c.width = c.block a :=
  take_block_append c a _

@[simp] theorem drop_width_cons {α : Type u} (c : BlockCode α) (a : α) (s : List α) :
    (encodeDataStack c (a :: s)).drop c.width = encodeDataStack c s :=
  drop_block_append c a _

theorem encodeDataStack_eq_nil_iff {α : Type u} (c : BlockCode α) (s : List α) :
    encodeDataStack c s = [] ↔ s = [] := by
  constructor
  · intro h
    have hlen := congrArg List.length h
    rw [length_encodeDataStack, List.length_nil] at hlen
    have hs : s.length = 0 := (Nat.mul_eq_zero.mp hlen).resolve_right
      (Nat.ne_of_gt c.width_pos)
    exact List.length_eq_zero_iff.mp hs
  · rintro rfl
    rfl

theorem encodeDataStack_injective {α : Type u} (c : BlockCode α) :
    Function.Injective (encodeDataStack c) := by
  intro s
  induction s with
  | nil =>
      intro t ht
      exact ((encodeDataStack_eq_nil_iff c t).mp ht.symm).symm
  | cons a s ih =>
      intro t ht
      cases t with
      | nil =>
          exact (List.cons_ne_nil a s ((encodeDataStack_eq_nil_iff c (a :: s)).mp ht)).elim
      | cons b t =>
          have hab : c.block a = c.block b := by
            simpa only [take_width_cons] using congrArg (List.take c.width) ht
          have hab' := c.injective_block hab
          subst b
          have hst : encodeDataStack c s = encodeDataStack c t := by
            simpa only [drop_width_cons] using congrArg (List.drop c.width) ht
          exact congrArg (List.cons a) (ih hst)

theorem take_prefix_boundary {α : Type u} (c : BlockCode α) (s t : List α) :
    (encodeDataStack c (s ++ t)).take (s.length * c.width) = encodeDataStack c s := by
  rw [encodeDataStack_append, ← length_encodeDataStack c s]
  exact List.take_left

theorem drop_prefix_boundary {α : Type u} (c : BlockCode α) (s t : List α) :
    (encodeDataStack c (s ++ t)).drop (s.length * c.width) = encodeDataStack c t := by
  rw [encodeDataStack_append, ← length_encodeDataStack c s]
  exact List.drop_left

/-- Removing one complete block is the encoding of stack pop, including empty
stacks. No partial-block boundary occurs. -/
theorem drop_width_eq_tail {α : Type u} (c : BlockCode α) (s : List α) :
    (encodeDataStack c s).drop c.width = encodeDataStack c s.tail := by
  cases s with
  | nil => simp
  | cons a s => exact drop_width_cons c a s

/-- Reading the first complete block recovers exactly the source stack's
optional top symbol, including the empty-stack case. -/
theorem readCodeOfEquiv_take_encode {α : Type u} {n : ℕ} (e : α ≃ Fin n)
    (s : List α) :
    readCodeOfEquiv e
        ((encodeDataStack (codeOfEquiv e) s).take (codeOfEquiv e).width) = s.head? := by
  cases s with
  | nil => simp
  | cons a s => simpa only [take_width_cons, List.head?_cons] using readCodeOfEquiv_block e a

@[simp] theorem boolCode_width : boolCode.width = 1 := rfl
@[simp] theorem boolCode_block (b : Bool) : boolCode.block b = [b] := rfl

@[simp] theorem encodeDataStack_boolCode (s : List Bool) : encodeDataStack boolCode s = s := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [ih]

@[simp] theorem encodeDataStack_codeOfBoolEquiv {α : Type u} (e : α ≃ Bool) (s : List α) :
    encodeDataStack (codeOfBoolEquiv e) s = s.map e := by
  induction s with
  | nil => rfl
  | cons a s ih =>
      change [e a] ++ encodeDataStack (codeOfBoolEquiv e) s = e a :: s.map e
      rw [ih]
      rfl

/-- Wrap data bits in `some`, reserving `none` exclusively for blank tape cells. -/
def tapeWord {α : Type u} (c : BlockCode α) (s : List α) : List (Option Bool) :=
  (encodeDataStack c s).map some

@[simp] theorem tapeWord_nil {α : Type u} (c : BlockCode α) : tapeWord c [] = [] := rfl

@[simp] theorem tapeWord_cons {α : Type u} (c : BlockCode α) (a : α) (s : List α) :
    tapeWord c (a :: s) = (c.block a).map some ++ tapeWord c s := by
  simp [tapeWord]

@[simp] theorem length_tapeWord {α : Type u} (c : BlockCode α) (s : List α) :
    (tapeWord c s).length = s.length * c.width := by simp [tapeWord]

theorem blank_not_mem_tapeWord {α : Type u} (c : BlockCode α) (s : List α) :
    none ∉ tapeWord c s := by simp [tapeWord]

theorem tapeWord_injective {α : Type u} (c : BlockCode α) :
    Function.Injective (tapeWord c) := by
  intro s t h
  apply encodeDataStack_injective c
  exact List.map_injective_iff.mpr (Option.some_injective Bool) h

theorem tapeWord_eq_nil_iff {α : Type u} (c : BlockCode α) (s : List α) :
    tapeWord c s = [] ↔ s = [] := by
  simp only [tapeWord, List.map_eq_nil_iff, encodeDataStack_eq_nil_iff]

@[simp] theorem tapeWord_boolCode (s : List Bool) : tapeWord boolCode s = s.map some := by
  simp [tapeWord]

/-- Optional representation with a *binary* bottom marker. This representation
is separate from `encodeDataStack`, which preserves the raw input format. -/
def encodeStack {α : Type u} (c : BlockCode (Option α)) (s : List α) : List Bool :=
  encodeDataStack c (s.map some ++ [none])

@[simp] theorem encodeStack_nil {α : Type u} (c : BlockCode (Option α)) :
    encodeStack c [] = c.block none := by simp [encodeStack]

@[simp] theorem encodeStack_cons {α : Type u} (c : BlockCode (Option α)) (a : α)
    (s : List α) : encodeStack c (a :: s) = c.block (some a) ++ encodeStack c s := by
  simp [encodeStack]

theorem encodeStack_injective {α : Type u} (c : BlockCode (Option α)) :
    Function.Injective (encodeStack c) := by
  intro s t h
  have hmap : s.map some = t.map some :=
    List.append_cancel_right (encodeDataStack_injective c h)
  exact List.map_injective_iff.mpr (Option.some_injective α) hmap

@[simp] theorem length_encodeStack {α : Type u} (c : BlockCode (Option α)) (s : List α) :
    (encodeStack c s).length = (s.length + 1) * c.width := by
  simp [encodeStack, c.length_block, Nat.add_mul]

theorem bottom_ne_symbol {α : Type u} (c : BlockCode (Option α)) (a : α) :
    c.block none ≠ c.block (some a) := by
  intro h
  exact Option.some_ne_none a (c.injective_block h).symm

@[simp] theorem take_width_encodeStack {α : Type u} (c : BlockCode (Option α))
    (s : List α) : (encodeStack c s).take c.width = c.block s.head? := by
  cases s with
  | nil => simpa only [encodeStack_nil, List.head?_nil, ← c.length_block none] using
      (List.take_length (l := c.block none))
  | cons a s => simpa only [encodeStack_cons, List.head?_cons] using
      take_block_append c (some a) (encodeStack c s)

theorem take_width_eq_bottom_iff {α : Type u} (c : BlockCode (Option α)) (s : List α) :
    (encodeStack c s).take c.width = c.block none ↔ s = [] := by
  rw [take_width_encodeStack]
  rw [c.injective_block.eq_iff]
  exact List.head?_eq_none_iff

@[simp] theorem drop_width_encodeStack_cons {α : Type u} (c : BlockCode (Option α))
    (a : α) (s : List α) :
    (encodeStack c (a :: s)).drop c.width = encodeStack c s := by
  rw [encodeStack_cons]
  exact drop_block_append c (some a) (encodeStack c s)

theorem drop_to_bottom {α : Type u} (c : BlockCode (Option α)) (s : List α) :
    (encodeStack c s).drop (s.length * c.width) = c.block none := by
  simpa only [encodeStack, List.length_map, encodeDataStack_cons, encodeDataStack_nil,
    List.append_nil] using drop_prefix_boundary c (s.map some) [none]

end SubexponentialSAT.StackEncoding

end OAI.Algorithms
