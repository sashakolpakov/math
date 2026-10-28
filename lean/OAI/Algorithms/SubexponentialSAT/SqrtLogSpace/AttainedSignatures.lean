import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRankSignature
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# First occurrences of attained keys

The subtype below is a specification of emissions, not a stored family.
The executable scan checks a candidate against its predecessors one at a time.
The key may be an entire integer row-signature; no coordinate projection occurs.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures

variable {N : ℕ} {κ : Type*} (key : Fin N → κ)

abbrev Representative := {i : Fin N // ∀ j, j < i → key j ≠ key i}

def toAttained (i : Representative key) : Set.range key := ⟨key i, i, rfl⟩

theorem toAttained_injective : Function.Injective (toAttained key) := by
  intro i j h
  have he : key i.val = key j.val := congrArg Subtype.val h
  apply Subtype.ext
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · exact (j.property i.val hij he).elim
  · exact hij
  · exact (i.property j.val hij he.symm).elim

theorem toAttained_surjective : Function.Surjective (toAttained key) := by
  classical
  intro y
  obtain ⟨j, hj⟩ := y.property
  have hex : ∃ i, key i = y.val := ⟨j, hj⟩
  let i := Fin.find (fun i => key i = y.val) hex
  have hkey := Fin.find_spec hex
  refine ⟨⟨i, ?_⟩, Subtype.ext hkey⟩
  intro j hj hji
  exact Fin.find_min hex hj (hji.trans hkey)

theorem toAttained_bijective : Function.Bijective (toAttained key) :=
  ⟨toAttained_injective key, toAttained_surjective key⟩

noncomputable def representativeEquiv : Representative key ≃ Set.range key :=
  Equiv.ofBijective (toAttained key) (toAttained_bijective key)

@[simp] theorem representativeEquiv_value (i : Representative key) :
    (representativeEquiv key i).val = key i := by
  rw [representativeEquiv, Equiv.ofBijective_apply]
  rfl

theorem card_representative : Nat.card (Representative key) = Nat.card (Set.range key) :=
  Nat.card_congr (representativeEquiv key)

theorem representative_exists (hN : 0 < N) : Nonempty (Representative key) :=
  ⟨⟨⟨0, hN⟩, by intro j hj; exact (Nat.not_lt_zero _ hj).elim⟩⟩

theorem card_representative_pos (hN : 0 < N) : 0 < Nat.card (Representative key) := by
  let _ := representative_exists key hN
  exact Nat.card_pos

theorem card_representative_one (key : Fin 1 → κ) : Nat.card (Representative key) = 1 := by
  have h : ∀ i : Fin 1, ∀ j : Fin 1, ¬j < i := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    omega
  let e : Representative key ≃ Fin 1 :=
    { toFun := Subtype.val
      invFun := fun i => ⟨i, fun j hij => (h i j hij).elim⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (by simp)

/-- Increasing numeric order of little-endian words, equivalently lexicographic
order after reversing the words. The empty head has its unique empty word. -/
def assignmentEquiv (h : ℕ) : Fin (2 ^ h) ≃ (Fin h → Bool) :=
  (Counters.wordEquiv h).trans (Equiv.vectorEquivFin Bool h)

theorem assignment_word (h : ℕ) (i : Fin (2 ^ h)) :
    List.ofFn (assignmentEquiv h i) =
      ExecCNFTupleEnumeration.fixedBits h i := by
  have hv := congrArg List.Vector.toList (List.Vector.ofFn_get (Counters.wordEquiv h i))
  change List.ofFn (List.Vector.get (Counters.wordEquiv h i)) =
    List.Vector.toList (Counters.wordEquiv h i)
  simpa only [List.Vector.toList_ofFn] using hv

/-- All stored constraint rows occur in this key, with integer arithmetic. -/
def integerKey {d h : ℕ} (A : Fin d → Fin h → ℤ) (i : Fin (2 ^ h)) : Fin d → ℤ :=
  OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound.boolSignature A (assignmentEquiv h i)

theorem card_integer_representative {d h : ℕ} (A : Fin d → Fin h → ℤ) :
    Nat.card (Representative (integerKey A)) =
      Nat.card (Set.range (OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound.boolSignature A)) := by
  rw [card_representative]
  have hr : Set.range (integerKey A) =
      Set.range (OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound.boolSignature A) :=
    (assignmentEquiv h).surjective.range_comp _
  rw [hr]

theorem card_integer_representative_le_rank {d h : ℕ} (A : Fin d → Fin h → ℤ)
    (W : ℕ) (hA : ∀ j i, |A j i| ≤ (W : ℤ)) :
    Nat.card (Representative (integerKey A)) ≤
      (2 * h * W + 1) ^ OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank.rowRank A := by
  rw [card_integer_representative]
  simpa using OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound.card_range_boolSignature_le_rank A W hA

theorem card_integer_representative_pos {d h : ℕ} (A : Fin d → Fin h → ℤ) :
    0 < Nat.card (Representative (integerKey A)) :=
  card_representative_pos _ (pow_pos (by omega) _)

theorem card_empty_head {d : ℕ} (A : Fin d → Fin 0 → ℤ) :
    Nat.card (Representative (integerKey A)) = 1 :=
  card_representative_one _

/-- The mutable duplicate latch has this proof-level recurrence. The actual
program implements it with a bounded word and one Boolean register. -/
def duplicateScan [DecidableEq κ] (key : ℕ → κ) (candidate : ℕ) : ℕ → Bool
  | 0 => false
  | bound + 1 => duplicateScan key candidate bound || decide (key bound = key candidate)

theorem duplicateScan_eq_true_iff [DecidableEq κ] (key : ℕ → κ) (candidate bound : ℕ) :
    duplicateScan key candidate bound = true ↔ ∃ j < bound, key j = key candidate := by
  induction bound with
  | zero => simp [duplicateScan]
  | succ bound ih =>
    simp only [duplicateScan, Bool.or_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro (⟨j, hj, he⟩ | he)
      · exact ⟨j, Nat.lt_succ_of_lt hj, he⟩
      · exact ⟨bound, Nat.lt_succ_self _, he⟩
    · rintro ⟨j, hj, he⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
      · exact Or.inl ⟨j, hj, he⟩
      · exact Or.inr he

theorem duplicateScan_eq_false_iff [DecidableEq κ] (key : ℕ → κ) (candidate bound : ℕ) :
    duplicateScan key candidate bound = false ↔ ∀ j < bound, key j ≠ key candidate := by
  rw [← Bool.not_eq_true, duplicateScan_eq_true_iff]
  simp

theorem rescan_emits_iff [DecidableEq κ] (key : ℕ → κ) (i : Fin N) :
    duplicateScan key i i = false ↔ ∀ j : Fin N, j < i → key j ≠ key i := by
  rw [duplicateScan_eq_false_iff]
  constructor
  · intro h j hj
    exact h j hj
  · intro h j hj
    exact h ⟨j, hj.trans i.isLt⟩ hj

/-- Both candidate and predecessor scans are charged even when a key loses.
This is a bound on scan counts, not an implementation cost theorem. -/
theorem rescan_comparisons_le (N : ℕ) : (∑ i : Fin N, i.val) ≤ N * N := by
  calc
    _ ≤ ∑ _i : Fin N, N := Finset.sum_le_sum (fun i _ => Nat.le_of_lt i.isLt)
    _ = N * N := by simp

theorem rescan_boolean_comparisons_le (h : ℕ) :
    (∑ i : Fin (2 ^ h), i.val) ≤ 4 ^ h := by
  have he : 2 ^ h * 2 ^ h = 4 ^ h := by rw [← mul_pow]; rfl
  simpa only [he] using rescan_comparisons_le (2 ^ h)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures
