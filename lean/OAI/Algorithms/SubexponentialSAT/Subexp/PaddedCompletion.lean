import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalExpectation

namespace OAI.Algorithms

/-!
# Explicit padded completion leaves

Every optional coordinate branches over the entire word alphabet. A real
coordinate updates the assignment; a dummy coordinate ignores the word.
Padding therefore implements the common-denominator multiplicity by actual
finite leaves rather than a multiplication of the resulting score.
-/

namespace SubexponentialSAT.Subexp.PaddedCompletion

open SubexponentialSAT.LocalExpectation
open SubexponentialSAT.Subexp.LocalExpectation

variable {I W J : Type*} [DecidableEq I]

/-- The natural value of a successful or unsuccessful collision test. -/
def boolValue (b : Bool) : ℕ := if b then 1 else 0

/-- A unary score is the list of successful Boolean leaves. -/
def successful (bs : List Bool) : List Bool := bs.filter id

def trueCount (bs : List Bool) : ℕ := (successful bs).length

theorem trueCount_eq_count (bs : List Bool) :
    trueCount bs = bs.count true := by
  have h : (fun b : Bool => b == true) = id := by
    funext b
    cases b <;> rfl
  simp only [List.count_eq_countP, List.countP_eq_length_filter, h,
    trueCount, successful]

/-- Real coordinates update the assignment; dummy coordinates consume a
choice without changing it. -/
def assignOptional (ω : I → W) (i : Option I) (w : W) : I → W :=
  match i with
  | none => ω
  | some j => Function.update ω j w

/-- Actual finite generation of collision Booleans, including every dummy
choice. No arithmetic scaling is used by this executable definition. -/
def leaves (alphabet : List W) (f : (I → W) → Bool) :
    List (Option I) → (I → W) → List Bool
  | [], ω => [f ω]
  | i :: remaining, ω =>
    alphabet.flatMap (fun w => leaves alphabet f remaining (assignOptional ω i w))

/-- Append enough ignored coordinates to reach the common support bound. -/
def paddedIndices (remaining : List I) (S : ℕ) : List (Option I) :=
  remaining.map some ++ List.replicate (S - remaining.length) none

def paddedLeaves (alphabet : List W) (f : (I → W) → Bool)
    (remaining : List I) (S : ℕ) (ω : I → W) : List Bool :=
  leaves alphabet f (paddedIndices remaining S) ω

private theorem length_flatMap_uniform {α β : Type*} (as : List α)
    (f : α → List β) (n : ℕ) (h : ∀ a, (f a).length = n) :
    (as.flatMap f).length = as.length * n := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, h, ih]
    rw [Nat.succ_mul, Nat.add_comm]

private theorem sum_map_const {α : Type*} (as : List α) (n : ℕ) :
    (as.map (fun _ => n)).sum = as.length * n := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    rw [Nat.succ_mul, Nat.add_comm]

theorem trueCount_flatMap {α : Type*} (as : List α) (f : α → List Bool) :
    trueCount (as.flatMap f) = (as.map (fun a => trueCount (f a))).sum := by
  simp only [trueCount, successful, List.filter_flatMap, List.length_flatMap]

@[simp] theorem trueCount_singleton (b : Bool) :
    trueCount [b] = boolValue b := by
  cases b <;> rfl

theorem leaves_length (alphabet : List W) (f : (I → W) → Bool)
    (remaining : List (Option I)) (ω : I → W) :
    (leaves alphabet f remaining ω).length =
      alphabet.length ^ remaining.length := by
  induction remaining generalizing ω with
  | nil => simp [leaves]
  | cons i remaining ih =>
    rw [leaves, length_flatMap_uniform alphabet _ _ (fun w => ih _)]
    simp only [List.length_cons, pow_succ, Nat.mul_comm]

omit [DecidableEq I] in
theorem paddedIndices_length (remaining : List I) (S : ℕ)
    (hS : remaining.length ≤ S) : (paddedIndices remaining S).length = S := by
  simp only [paddedIndices, List.length_append, List.length_map, List.length_replicate]
  exact Nat.add_sub_of_le hS

theorem paddedLeaves_length (alphabet : List W) (f : (I → W) → Bool)
    (remaining : List I) (S : ℕ) (hS : remaining.length ≤ S) (ω : I → W) :
    (paddedLeaves alphabet f remaining S ω).length = alphabet.length ^ S := by
  rw [paddedLeaves, leaves_length, paddedIndices_length remaining S hS]

/-- Dummy coordinates repeat each terminal Boolean once for every tuple of
dummy word choices. -/
theorem trueCount_dummy (alphabet : List W) (f : (I → W) → Bool)
    (n : ℕ) (ω : I → W) :
    trueCount (leaves alphabet f (List.replicate n none) ω) =
      alphabet.length ^ n * boolValue (f ω) := by
  induction n with
  | zero => simp [leaves]
  | succ n ih =>
    simp only [List.replicate_succ, leaves, trueCount_flatMap, assignOptional]
    simp_rw [ih]
    rw [sum_map_const]
    simp only [pow_succ]
    ac_rfl

/-- Padding is precisely the common-denominator factor in the natural
completion count. This equality holds even before imposing the size bound. -/
theorem trueCount_some_append_dummy (alphabet : List W) (f : (I → W) → Bool)
    (remaining : List I) (n : ℕ) (ω : I → W) :
    trueCount (leaves alphabet f
      (remaining.map some ++ List.replicate n none) ω) =
        alphabet.length ^ n *
          completionCount alphabet (fun η => boolValue (f η)) remaining ω := by
  induction remaining generalizing ω with
  | nil => simpa [completionCount] using trueCount_dummy alphabet f n ω
  | cons i remaining ih =>
    simp only [List.map_cons, List.cons_append, leaves, trueCount_flatMap,
      assignOptional, completionCount]
    simp_rw [ih]
    exact List.sum_map_mul_left alphabet
      (fun w => completionCount alphabet (fun η => boolValue (f η))
        remaining (Function.update ω i w)) (alphabet.length ^ n)

theorem trueCount_paddedLeaves (alphabet : List W) (f : (I → W) → Bool)
    (remaining : List I) (S : ℕ) (ω : I → W) :
    trueCount (paddedLeaves alphabet f remaining S ω) =
      alphabet.length ^ (S - remaining.length) *
        completionCount alphabet (fun η => boolValue (f η)) remaining ω :=
  trueCount_some_append_dummy alphabet f remaining (S - remaining.length) ω

theorem boolValue_decide_one (n : ℕ) (hn : n ≤ 1) :
    boolValue (decide (n = 1)) = n := by
  cases n with
  | zero => rfl
  | succ n =>
    have h : n = 0 := by omega
    subst n
    rfl

/-- Concatenate all padded local completion trees. This is a single finite
Boolean input whose successful leaves encode the common numerator. -/
def numeratorLeaves (alphabet : List W) (terms : List J)
    (f : J → (I → W) → ℕ) (support : J → Finset I) (S : ℕ)
    (remaining : List I) (ω : I → W) : List Bool :=
  terms.flatMap (fun j =>
    paddedLeaves alphabet (fun η => decide (f j η = 1))
      (active (support j) remaining) S ω)

/-- The successful-leaf count is exactly the existing natural common
numerator, for arbitrary bounded zero/one local terms. -/
theorem numeratorLeaves_trueCount (alphabet : List W) (terms : List J)
    (f : J → (I → W) → ℕ) (hf : ∀ j η, f j η ≤ 1)
    (support : J → Finset I) (S : ℕ) (remaining : List I) (ω : I → W) :
    trueCount (numeratorLeaves alphabet terms f support S remaining ω) =
      commonNumerator alphabet terms f support S remaining ω := by
  rw [numeratorLeaves, trueCount_flatMap]
  unfold commonNumerator
  congr 1
  apply List.map_congr_left
  intro j _
  rw [trueCount_paddedLeaves]
  have h : (fun η => boolValue (decide (f j η = 1))) = f j := by
    funext η
    exact boolValue_decide_one (f j η) (hf j η)
  rw [h]
  rfl

/-- Every term contributes exactly q^S leaves once its free support is
bounded by S. -/
theorem numeratorLeaves_length (alphabet : List W) (terms : List J)
    (f : J → (I → W) → ℕ) (support : J → Finset I) (S : ℕ)
    (remaining : List I) (hS : ∀ j, (active (support j) remaining).length ≤ S)
    (ω : I → W) :
    (numeratorLeaves alphabet terms f support S remaining ω).length =
      terms.length * alphabet.length ^ S := by
  unfold numeratorLeaves
  apply length_flatMap_uniform
  intro j
  exact paddedLeaves_length alphabet _ _ S (hS j) ω

theorem successful_numeratorLeaves_length (alphabet : List W) (terms : List J)
    (f : J → (I → W) → ℕ) (hf : ∀ j η, f j η ≤ 1)
    (support : J → Finset I) (S : ℕ) (remaining : List I) (ω : I → W) :
    (successful (numeratorLeaves alphabet terms f support S remaining ω)).length =
      commonNumerator alphabet terms f support S remaining ω :=
  numeratorLeaves_trueCount alphabet terms f hf support S remaining ω

theorem numeratorLeaves_count_true (alphabet : List W) (terms : List J)
    (f : J → (I → W) → ℕ) (hf : ∀ j η, f j η ≤ 1)
    (support : J → Finset I) (S : ℕ) (remaining : List I) (ω : I → W) :
    (numeratorLeaves alphabet terms f support S remaining ω).count true =
      commonNumerator alphabet terms f support S remaining ω := by
  rw [← trueCount_eq_count]
  exact numeratorLeaves_trueCount alphabet terms f hf support S remaining ω

section PairObjective

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpTypeVariance SubexponentialSAT.SlotAssignment

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (P : SubexponentialSAT.Factor.Pattern V E) {r Q Δ : ℕ} [NeZero r] (slots : SlotMap P Δ)

/-- The concrete concatenated collision leaves for all ordered vertex pairs. -/
def pairLeaves (alphabet : List (Word r Q)) (vertices : List V)
    (remaining : List (SeedIndex V E Δ)) (ω : Assignment V E r Q Δ) : List Bool :=
  numeratorLeaves alphabet (vertices.product vertices) (naturalPairTerm P slots)
    (fun pair => pairSupport P slots pair.1 pair.2) (2 * (Δ + 1)) remaining ω

omit [Fintype V] [NeZero r] in
theorem pairLeaves_trueCount (alphabet : List (Word r Q)) (vertices : List V)
    (remaining : List (SeedIndex V E Δ)) (ω : Assignment V E r Q Δ) :
    trueCount (pairLeaves P slots alphabet vertices remaining ω) =
      pairNumerator P slots alphabet vertices remaining ω :=
  numeratorLeaves_trueCount alphabet (vertices.product vertices)
    (naturalPairTerm P slots) (naturalPairTerm_le P slots)
    (fun pair => pairSupport P slots pair.1 pair.2) (2 * (Δ + 1)) remaining ω

omit [Fintype V] [NeZero r] in
theorem pairLeaves_length (alphabet : List (Word r Q)) (vertices : List V)
    (remaining : List (SeedIndex V E Δ)) (hr : remaining.Nodup)
    (ω : Assignment V E r Q Δ) :
    (pairLeaves P slots alphabet vertices remaining ω).length =
      vertices.length ^ 2 * alphabet.length ^ (2 * (Δ + 1)) := by
  unfold pairLeaves
  rw [numeratorLeaves_length]
  · have length_product (xs ys : List V) :
        (xs.product ys).length = xs.length * ys.length := by
      induction xs with
      | nil => simp [List.product]
      | cons x xs ih =>
        change (List.map (Prod.mk x) ys ++ xs.product ys).length =
          (x :: xs).length * ys.length
        rw [List.length_append, List.length_map, ih, List.length_cons,
          Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [length_product, pow_two]
  · intro pair
    exact (active_length_le _ _ hr).trans (pairSupport_card_le P slots pair.1 pair.2)

omit [Fintype V] in
omit [NeZero r] in
/-- The actual leaf list has exactly D²N² entries for a complete word
alphabet, not just an abstract numerical upper bound. -/
theorem pairLeaves_length_eq_block (alphabet : List (Word r Q))
    (haNodup : alphabet.Nodup) (haFull : ∀ w, w ∈ alphabet) (vertices : List V)
    (remaining : List (SeedIndex V E Δ)) (hr : remaining.Nodup)
    (ω : Assignment V E r Q Δ) :
    (pairLeaves P slots alphabet vertices remaining ω).length =
      vertices.length ^ 2 * (blockSize r Q Δ) ^ 2 := by
  rw [pairLeaves_length P slots alphabet vertices remaining hr ω,
    alphabet_pair_power alphabet haNodup haFull]

omit [Fintype V] [NeZero r] in
theorem successful_pairLeaves_length (alphabet : List (Word r Q)) (vertices : List V)
    (remaining : List (SeedIndex V E Δ)) (ω : Assignment V E r Q Δ) :
    (successful (pairLeaves P slots alphabet vertices remaining ω)).length =
      pairNumerator P slots alphabet vertices remaining ω :=
  pairLeaves_trueCount P slots alphabet vertices remaining ω

omit [Fintype V] [NeZero r] in
theorem pairLeaves_count_true (alphabet : List (Word r Q)) (vertices : List V)
    (remaining : List (SeedIndex V E Δ)) (ω : Assignment V E r Q Δ) :
    (pairLeaves P slots alphabet vertices remaining ω).count true =
      pairNumerator P slots alphabet vertices remaining ω := by
  rw [← trueCount_eq_count]
  exact pairLeaves_trueCount P slots alphabet vertices remaining ω

end PairObjective

end SubexponentialSAT.Subexp.PaddedCompletion

end OAI.Algorithms
