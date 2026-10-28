import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SAT

namespace OAI.Algorithms

/-!
# Finite reduction and leaf-search interfaces

These lemmas connect a finite OR reduction with executable Boolean leaf tests.
`scan` records the number of calls to its supplied leaf test.  This is **not**
a count of bit operations or Turing-machine transitions.  A machine realization
of the leaf test, the reduction, and this search is a separate obligation.

No declaration here asserts the existence of the manuscript's fast counter.
-/

namespace SubexponentialSAT.Interfaces

universe u v

/-- Search in order and stop at the first accepting leaf. The second component
counts calls to `test`, not the implementation cost of those calls. -/
def scan {α : Type u} (test : α → Bool) : List α → Bool × ℕ
  | [] => (false, 0)
  | x :: xs =>
      if test x then (true, 1)
      else
        let rest := scan test xs
        (rest.1, rest.2 + 1)

@[simp] theorem scan_nil {α : Type u} (test : α → Bool) :
    scan test [] = (false, 0) := rfl

/-- The short-circuit search has the ordinary finite-OR semantics. -/
theorem scan_accepts_iff {α : Type u} (test : α → Bool) (xs : List α) :
    (scan test xs).1 = true ↔ ∃ x ∈ xs, test x = true := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
      cases hx : test x <;> simp [scan, hx, ih]

/-- The call count is bounded by the number of explicitly supplied leaves. -/
theorem scan_calls_le_length {α : Type u} (test : α → Bool) (xs : List α) :
    (scan test xs).2 ≤ xs.length := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
      cases hx : test x with
      | false => simpa [scan, hx] using Nat.add_le_add_right ih 1
      | true => simp [scan, hx]

/-- A rejecting search tests every leaf. This also covers an empty leaf list. -/
theorem scan_reject_calls {α : Type u} (test : α → Bool) (xs : List α)
    (hreject : (scan test xs).1 = false) :
    (scan test xs).2 = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hx : test x with
      | false =>
          have htail : (scan test xs).1 = false := by simpa [scan, hx] using hreject
          simpa [scan, hx] using ih htail
      | true => simp [scan, hx] at hreject

/-- The finite OR reduction need preserve only existence, not disjointness or
the number of witnesses. Every displayed hypothesis is a semantic proof
obligation; this theorem supplies no reduction algorithm or fast leaf test. -/
theorem finite_or_reduction_correct
    {α : Type u} {β : Type v} (P : α → Prop) (Q : β → Prop)
    (reduce : α → List β) (test : β → Bool)
    (hreduce : ∀ x, P x ↔ ∃ y ∈ reduce x, Q y)
    (htest : ∀ x, ∀ y ∈ reduce x, test y = true ↔ Q y) (x : α) :
    (scan test (reduce x)).1 = true ↔ P x := by
  rw [scan_accepts_iff, hreduce x]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, (htest x y hy).mp h⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, (htest x y hy).mpr h⟩

/-- Deciding a finite list from its supplied nonnegative integer counts. -/
def scanCounts {α : Type u} (countLeaf : α → ℕ) (leaves : List α) : Bool × ℕ :=
  scan (fun leaf => countLeaf leaf != 0) leaves

theorem scanCounts_accepts_iff {α : Type u} (countLeaf : α → ℕ) (leaves : List α) :
    (scanCounts countLeaf leaves).1 = true ↔ ∃ leaf ∈ leaves, 0 < countLeaf leaf := by
  simp only [scanCounts, scan_accepts_iff, bne_iff_ne, ne_eq, Nat.pos_iff_ne_zero]

/-- The main algorithm can test a lifted ring value for zero directly, without
first decoding the represented integer count. -/
def scanNonzero {α : Type u} {R : Type v} [Zero R] [DecidableEq R]
    (value : α → R) (leaves : List α) : Bool × ℕ :=
  scan (fun leaf => decide (value leaf ≠ 0)) leaves

theorem scanNonzero_accepts_iff {α : Type u} {R : Type v} [Zero R] [DecidableEq R]
    (value : α → R) (leaves : List α) :
    (scanNonzero value leaves).1 = true ↔ ∃ leaf ∈ leaves, value leaf ≠ 0 := by
  simp only [scanNonzero, scan_accepts_iff, decide_eq_true_eq]

section SAT

variable {V : Type u} [DecidableEq V] [Fintype V]

/-- Correctness glue for Section 6.1. `hcover` is furnished by sparsification;
`hcount` must be furnished by an actual leaf counter. They do not require
disjoint leaves, and duplicate leaves do not affect acceptance. -/
theorem sat_reduction_correct (F : SAT.CNF V) (leaves : List (SAT.CNF V))
    (countLeaf : SAT.CNF V → ℕ)
    (hcover : SAT.Satisfiable F ↔ ∃ G ∈ leaves, SAT.Satisfiable G)
    (hcount : ∀ G ∈ leaves, countLeaf G = SAT.count G) :
    (scanCounts countLeaf leaves).1 = true ↔ SAT.Satisfiable F := by
  rw [scanCounts_accepts_iff, hcover]
  constructor
  · rintro ⟨G, hG, hpos⟩
    exact ⟨G, hG, (SAT.count_pos_iff G).mp ((hcount G hG) ▸ hpos)⟩
  · rintro ⟨G, hG, hsat⟩
    refine ⟨G, hG, ?_⟩
    rw [hcount G hG]
    exact (SAT.count_pos_iff G).mpr hsat

/-- Concrete exhaustive leaf testing is sufficient for the correctness bridge.
This theorem makes no fast-running-time claim. -/
theorem exhaustive_reduction_correct (F : SAT.CNF V) (leaves : List (SAT.CNF V))
    (hcover : SAT.Satisfiable F ↔ ∃ G ∈ leaves, SAT.Satisfiable G) :
    (scanCounts SAT.count leaves).1 = true ↔ SAT.Satisfiable F :=
  sat_reduction_correct F leaves SAT.count hcover (by intros; rfl)

/-- The exact interface used by the manuscript's final `H(0) ≠ 0` test.
`hzero` must come from the prime-power count theorem and count bound; it is
not an assumption that an arbitrary residue-field count suffices. -/
theorem sat_residue_reduction_correct {R : Type v} [Zero R] [DecidableEq R]
    (F : SAT.CNF V) (leaves : List (SAT.CNF V)) (value : SAT.CNF V → R)
    (hcover : SAT.Satisfiable F ↔ ∃ G ∈ leaves, SAT.Satisfiable G)
    (hzero : ∀ G ∈ leaves, value G = 0 ↔ SAT.count G = 0) :
    (scanNonzero value leaves).1 = true ↔ SAT.Satisfiable F := by
  rw [scanNonzero_accepts_iff, hcover]
  have hleaf : ∀ G ∈ leaves, value G ≠ 0 ↔ SAT.Satisfiable G := by
    intro G hG
    rw [← SAT.count_pos_iff, Nat.pos_iff_ne_zero]
    exact not_congr (hzero G hG)
  constructor
  · rintro ⟨G, hG, hne⟩
    exact ⟨G, hG, (hleaf G hG).mp hne⟩
  · rintro ⟨G, hG, hsat⟩
    exact ⟨G, hG, (hleaf G hG).mpr hsat⟩

end SAT

end SubexponentialSAT.Interfaces

end OAI.Algorithms
