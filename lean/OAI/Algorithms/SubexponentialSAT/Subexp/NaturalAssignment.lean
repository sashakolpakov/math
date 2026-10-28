import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalExpectation
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentEnumeration
import OAI.Algorithms.SubexponentialSAT.Subexp.PaddedCompletion

namespace OAI.Algorithms

/-!
# Conditional assignment by natural-number comparisons

The executable chooser and all of its scores use natural numbers. A rational
common-denominator identity is used only to prove that every comparison,
including ties, agrees with the previously verified conditional-expectation
algorithm. Score execution enumerates only the active local pair support.
-/

namespace SubexponentialSAT.Subexp.NaturalAssignment

open scoped BigOperators

section Search

variable {A : Type*}

/-- Earliest minimum in an explicit nonempty list, using only natural scores. -/
def chooseMinNat (score : A → ℕ) (a : A) : List A → A
  | [] => a
  | b :: bs =>
      let c := chooseMinNat score b bs
      if score a ≤ score c then a else c

/-- The chooser depends only on the ordering of scores, including equality. -/
theorem chooseMinNat_eq_chooseMin (natural : A → ℕ) (rational : A → ℚ)
    (horder : ∀ x y, rational x ≤ rational y ↔ natural x ≤ natural y)
    (a : A) (tail : List A) :
    chooseMinNat natural a tail =
      SubexponentialSAT.ConditionalExpectation.chooseMin rational a tail := by
  induction tail generalizing a with
  | nil => rfl
  | cons b bs ih =>
      simp only [chooseMinNat, SubexponentialSAT.ConditionalExpectation.chooseMin, ih, horder]

theorem chooseMinNat_mem (score : A → ℕ) (a : A) (tail : List A) :
    chooseMinNat score a tail ∈ a :: tail := by
  induction tail generalizing a with
  | nil => simp [chooseMinNat]
  | cons b bs ih =>
      simp only [chooseMinNat]
      split_ifs
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (ih b)

/-- Sequential assignment with a natural-number evaluator. -/
def assignNat (a : A) (tail : List A) (evaluate : ℕ → List A → ℕ) :
    ℕ → List A → List A
  | 0, fixed => fixed
  | n + 1, fixed =>
      let next := chooseMinNat (fun x => evaluate n (x :: fixed)) a tail
      assignNat a tail evaluate n (next :: fixed)

theorem assignNat_eq_assignWithEvaluator (a : A) (tail : List A)
    (natural : ℕ → List A → ℕ) (rational : ℕ → List A → ℚ)
    (horder : ∀ n fixed x y,
      rational n (x :: fixed) ≤ rational n (y :: fixed) ↔
        natural n (x :: fixed) ≤ natural n (y :: fixed))
    (n : ℕ) (fixed : List A) :
    assignNat a tail natural n fixed =
      SubexponentialSAT.ConditionalExpectation.assignWithEvaluator a tail rational n fixed := by
  induction n generalizing fixed with
  | zero => rfl
  | succ n ih =>
      have hchoice := chooseMinNat_eq_chooseMin
        (fun x => natural n (x :: fixed)) (fun x => rational n (x :: fixed))
        (horder n fixed) a tail
      simp only [assignNat, SubexponentialSAT.ConditionalExpectation.assignWithEvaluator,
        hchoice, ih]

/-- Instrumented natural chooser. The second component counts terminal calls
reported by the executed score evaluations. -/
def chooseWithCostNat (score : A → ℕ × ℕ) (a : A) : List A → A × ℕ
  | [] => (a, 0)
  | b :: bs =>
      let c := chooseWithCostNat score b bs
      let left := score a
      let right := score c.1
      (if left.1 ≤ right.1 then a else c.1, c.2 + left.2 + right.2)

theorem chooseWithCostNat_eq (natural : A → ℕ × ℕ) (rational : A → ℚ × ℕ)
    (horder : ∀ x y, (rational x).1 ≤ (rational y).1 ↔
      (natural x).1 ≤ (natural y).1)
    (hcount : ∀ x, (natural x).2 = (rational x).2)
    (a : A) (tail : List A) :
    chooseWithCostNat natural a tail =
      SubexponentialSAT.LocalExpectation.chooseWithCost rational a tail := by
  induction tail generalizing a with
  | nil => rfl
  | cons b bs ih =>
      simp only [chooseWithCostNat, SubexponentialSAT.LocalExpectation.chooseWithCost,
        ih, horder, hcount]

/-- Instrumented sequential natural search, retaining the same finite loops. -/
def assignWithCostNat (a : A) (tail : List A)
    (evaluate : ℕ → List A → ℕ × ℕ) : ℕ → List A → List A × ℕ
  | 0, fixed => (fixed, 0)
  | n + 1, fixed =>
      let next := chooseWithCostNat (fun x => evaluate n (x :: fixed)) a tail
      let result := assignWithCostNat a tail evaluate n (next.1 :: fixed)
      (result.1, next.2 + result.2)

theorem assignWithCostNat_eq (a : A) (tail : List A)
    (natural : ℕ → List A → ℕ × ℕ) (rational : ℕ → List A → ℚ × ℕ)
    (horder : ∀ n fixed x y,
      (rational n (x :: fixed)).1 ≤ (rational n (y :: fixed)).1 ↔
        (natural n (x :: fixed)).1 ≤ (natural n (y :: fixed)).1)
    (hcount : ∀ n fixed, (natural n fixed).2 = (rational n fixed).2)
    (n : ℕ) (fixed : List A) :
    assignWithCostNat a tail natural n fixed =
      SubexponentialSAT.LocalExpectation.assignWithCost a tail rational n fixed := by
  induction n generalizing fixed with
  | zero => rfl
  | succ n ih =>
      have hchoice := chooseWithCostNat_eq
        (fun x => natural n (x :: fixed)) (fun x => rational n (x :: fixed))
        (horder n fixed) (fun x => hcount n (x :: fixed)) a tail
      simp only [assignWithCostNat, SubexponentialSAT.LocalExpectation.assignWithCost,
        hchoice, ih]

end Search

section LocalCounts

variable {I W J : Type*} [DecidableEq I]

/-- Count successful completions and the leaf tests actually performed. -/
def completionCountCounted (alphabet : List W) (f : (I → W) → ℕ) :
    List I → (I → W) → ℕ × ℕ
  | [], ω => (f ω, 1)
  | i :: remaining, ω =>
      let children := alphabet.map (fun w =>
        completionCountCounted alphabet f remaining (Function.update ω i w))
      ((children.map Prod.fst).sum, (children.map Prod.snd).sum)

theorem completionCountCounted_value (alphabet : List W) (f : (I → W) → ℕ)
    (remaining : List I) (ω : I → W) :
    (completionCountCounted alphabet f remaining ω).1 =
      SubexponentialSAT.Subexp.LocalExpectation.completionCount alphabet f remaining ω := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i remaining ih =>
      simp [completionCountCounted, SubexponentialSAT.Subexp.LocalExpectation.completionCount,
        List.map_map, Function.comp_def, ih]

theorem completionCountCounted_calls (alphabet : List W) (f : (I → W) → ℕ)
    (remaining : List I) (ω : I → W) :
    (completionCountCounted alphabet f remaining ω).2 =
      alphabet.length ^ remaining.length := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i remaining ih =>
      simp [completionCountCounted, List.map_map, Function.comp_def, ih,
        pow_succ, Nat.mul_comm]

/-- The natural common-numerator algorithm with its actual terminal-call
counter. Multiplications and list operations are separate cost obligations. -/
def commonNumeratorCounted (alphabet : List W) (terms : List J)
    (f : J → (I → W) → ℕ) (support : J → Finset I) (S : ℕ)
    (remaining : List I) (ω : I → W) : ℕ × ℕ :=
  let results := terms.map fun j =>
    let result := completionCountCounted alphabet (f j)
      (SubexponentialSAT.LocalExpectation.active (support j) remaining) ω
    (alphabet.length ^ (S - (SubexponentialSAT.LocalExpectation.active (support j) remaining).length) *
      result.1, result.2)
  ((results.map Prod.fst).sum, (results.map Prod.snd).sum)

theorem commonNumeratorCounted_value (alphabet : List W) (terms : List J)
    (f : J → (I → W) → ℕ) (support : J → Finset I) (S : ℕ)
    (remaining : List I) (ω : I → W) :
    (commonNumeratorCounted alphabet terms f support S remaining ω).1 =
      SubexponentialSAT.Subexp.LocalExpectation.commonNumerator alphabet terms f support S remaining ω := by
  simp [commonNumeratorCounted, SubexponentialSAT.Subexp.LocalExpectation.commonNumerator,
    SubexponentialSAT.Subexp.LocalExpectation.scaledCount, List.map_map, Function.comp_def,
    completionCountCounted_value]

theorem commonNumeratorCounted_calls (alphabet : List W) (terms : List J)
    (f : J → (I → W) → ℕ) (support : J → Finset I) (S : ℕ)
    (remaining : List I) (ω : I → W) :
    (commonNumeratorCounted alphabet terms f support S remaining ω).2 =
      (terms.map fun j =>
        alphabet.length ^ (SubexponentialSAT.LocalExpectation.active (support j) remaining).length).sum := by
  simp [commonNumeratorCounted, List.map_map, Function.comp_def, completionCountCounted_calls]

end LocalCounts

section PairScores

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpTypeVariance SubexponentialSAT.SlotAssignment
open SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.LocalExpectation
  (active active_length_le decode indexCode sequentialEvaluator localAssign)

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (P : SubexponentialSAT.Factor.Pattern V E) {r Q Δ : ℕ} [NeZero r] (slots : SlotMap P Δ)

/-- The natural zero/one collision test on numbered seed coordinates. -/
def numberedNaturalPairTerm (indices : List (SeedIndex V E Δ)) (pair : V × V)
    (ξ : ℕ → Word r Q) : ℕ :=
  naturalPairTerm P slots pair (fun i => ξ (indexCode indices i))

omit [Fintype V] [NeZero r] in
theorem numberedNaturalPairTerm_cast (indices : List (SeedIndex V E Δ))
    (pair : V × V) (ξ : ℕ → Word r Q) :
    (numberedNaturalPairTerm P slots indices pair ξ : ℚ) =
      numberedPairTerm P slots indices pair ξ := by
  exact naturalPairTerm_cast P slots pair _

omit [Fintype V] [NeZero r] in
theorem numberedNaturalPairTerm_le (indices : List (SeedIndex V E Δ))
    (pair : V × V) (ξ : ℕ → Word r Q) :
    numberedNaturalPairTerm P slots indices pair ξ ≤ 1 :=
  naturalPairTerm_le P slots pair _

/-- A common natural numerator for the same local pairs as the verified
numbered evaluator. No rational arithmetic is executed by this definition. -/
def numberedPairNumerator (alphabet : List (Word r Q)) (vertices : List V)
    (indices : List (SeedIndex V E Δ)) (remaining : List ℕ)
    (ξ : ℕ → Word r Q) : ℕ :=
  commonNumerator alphabet (vertices.product vertices)
    (numberedNaturalPairTerm P slots indices) (numberedPairSupport P slots indices)
    (2 * (Δ + 1)) remaining ξ

omit [Fintype V] [NeZero r] in
theorem numberedPairNumerator_le (alphabet : List (Word r Q)) (vertices : List V)
    (indices : List (SeedIndex V E Δ)) (remaining : List ℕ)
    (hr : remaining.Nodup) (ξ : ℕ → Word r Q) :
    numberedPairNumerator P slots alphabet vertices indices remaining ξ ≤
      vertices.length ^ 2 * alphabet.length ^ (2 * (Δ + 1)) := by
  have h := commonNumerator_le alphabet (vertices.product vertices)
    (numberedNaturalPairTerm P slots indices)
    (numberedNaturalPairTerm_le P slots indices)
    (numberedPairSupport P slots indices) (2 * (Δ + 1)) remaining
    (fun pair => (active_length_le _ _ hr).trans
      (numberedPairSupport_card_le P slots indices pair)) ξ
  have hprod : (vertices.product vertices).length = vertices.length * vertices.length :=
    List.length_product _ _
  simpa only [numberedPairNumerator, hprod, pow_two] using h

omit [Fintype V] [NeZero r] in
/-- The common denominator is N² for a complete, duplicate-free word list. -/
theorem numberedPairNumerator_le_block_square (alphabet : List (Word r Q))
    (haNodup : alphabet.Nodup) (haFull : ∀ w, w ∈ alphabet)
    (vertices : List V) (indices : List (SeedIndex V E Δ))
    (remaining : List ℕ) (hr : remaining.Nodup) (ξ : ℕ → Word r Q) :
    numberedPairNumerator P slots alphabet vertices indices remaining ξ ≤
      vertices.length ^ 2 * (blockSize r Q Δ) ^ 2 := by
  simpa only [alphabet_pair_power (Δ := Δ) alphabet haNodup haFull] using
    numberedPairNumerator_le P slots alphabet vertices indices remaining hr ξ

/-- Sequential candidate scores enumerate only the as-yet-unassigned numbered
coordinates read by each pair of input coordinates. -/
def sequentialNumerator (alphabet : List (Word r Q)) (vertices : List V)
    (indices : List (SeedIndex V E Δ)) (default : Word r Q)
    (n : ℕ) (fixed : List (Word r Q)) : ℕ :=
  numberedPairNumerator P slots alphabet vertices indices
    (List.range' fixed.length n) (decode default fixed)

omit [Fintype V] [NeZero r] in
theorem sequentialNumerator_le (alphabet : List (Word r Q))
    (haNodup : alphabet.Nodup) (haFull : ∀ w, w ∈ alphabet)
    (vertices : List V) (indices : List (SeedIndex V E Δ)) (default : Word r Q)
    (n : ℕ) (fixed : List (Word r Q)) :
    sequentialNumerator P slots alphabet vertices indices default n fixed ≤
      vertices.length ^ 2 * (blockSize r Q Δ) ^ 2 :=
  numberedPairNumerator_le_block_square P slots alphabet haNodup haFull
    vertices indices _ List.nodup_range' _

private theorem size_square_product_bound (D N : ℕ) :
    (D ^ 2 * N ^ 2).size ≤ 2 * D.size + 2 * N.size + 1 := by
  have hD : D ≤ 2 ^ D.size := (Nat.lt_size_self D).le
  have hN : N ≤ 2 ^ N.size := (Nat.lt_size_self N).le
  have hDs : D ^ 2 ≤ (2 ^ D.size) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hD hD
  have hNs : N ^ 2 ≤ (2 ^ N.size) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hN hN
  apply Nat.size_le.mpr
  have hprod := Nat.mul_le_mul hDs hNs
  have hp : (2 ^ D.size) ^ 2 * (2 ^ N.size) ^ 2 =
      2 ^ (2 * D.size + 2 * N.size) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [hp] at hprod
  exact hprod.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

omit [Fintype V] [NeZero r] in
/-- Binary size of every actual sequential numerator used by the chooser. -/
theorem sequentialNumerator_bitSize_le (alphabet : List (Word r Q))
    (haNodup : alphabet.Nodup) (haFull : ∀ w, w ∈ alphabet)
    (vertices : List V) (indices : List (SeedIndex V E Δ)) (default : Word r Q)
    (n : ℕ) (fixed : List (Word r Q)) :
    (sequentialNumerator P slots alphabet vertices indices default n fixed).size ≤
      2 * vertices.length.size + 2 * (blockSize r Q Δ).size + 1 :=
  (Nat.size_le_size (sequentialNumerator_le P slots alphabet haNodup haFull
    vertices indices default n fixed)).trans
    (size_square_product_bound vertices.length (blockSize r Q Δ))

/-- Materialize the same numerator as successful Boolean leaves, using dummy
choices to pad each pair's local support to 2(Δ+1) words. -/
def sequentialNumeratorLeaves (alphabet : List (Word r Q)) (vertices : List V)
    (indices : List (SeedIndex V E Δ)) (default : Word r Q)
    (n : ℕ) (fixed : List (Word r Q)) : List Bool :=
  PaddedCompletion.numeratorLeaves alphabet (vertices.product vertices)
    (numberedNaturalPairTerm P slots indices) (numberedPairSupport P slots indices)
    (2 * (Δ + 1)) (List.range' fixed.length n) (decode default fixed)

omit [Fintype V] [NeZero r] in
/-- The actual successful-leaf list is a unary representation of the score. -/
theorem sequentialNumeratorLeaves_trueCount (alphabet : List (Word r Q))
    (vertices : List V) (indices : List (SeedIndex V E Δ)) (default : Word r Q)
    (n : ℕ) (fixed : List (Word r Q)) :
    (PaddedCompletion.successful
      (sequentialNumeratorLeaves P slots alphabet vertices indices default n fixed)).length =
        sequentialNumerator P slots alphabet vertices indices default n fixed :=
  PaddedCompletion.successful_numeratorLeaves_length _ _ _
    (numberedNaturalPairTerm_le P slots indices) _ _ _ _

omit [Fintype V] in
omit [NeZero r] in
theorem sequentialNumeratorLeaves_length (alphabet : List (Word r Q))
    (haNodup : alphabet.Nodup) (haFull : ∀ w, w ∈ alphabet)
    (vertices : List V) (indices : List (SeedIndex V E Δ)) (default : Word r Q)
    (n : ℕ) (fixed : List (Word r Q)) :
    (sequentialNumeratorLeaves P slots alphabet vertices indices default n fixed).length =
      vertices.length ^ 2 * (blockSize r Q Δ) ^ 2 := by
  have h := PaddedCompletion.numeratorLeaves_length alphabet (vertices.product vertices)
    (numberedNaturalPairTerm P slots indices) (numberedPairSupport P slots indices)
    (2 * (Δ + 1)) (List.range' fixed.length n)
    (fun pair => (active_length_le _ _ List.nodup_range').trans
      (numberedPairSupport_card_le P slots indices pair)) (decode default fixed)
  have hprod : (vertices.product vertices).length = vertices.length * vertices.length :=
    List.length_product _ _
  simpa only [sequentialNumeratorLeaves, hprod, pow_two,
    alphabet_pair_power (Δ := Δ) alphabet haNodup haFull] using h

omit [NeZero r] in
/-- Exact common-denominator specification; this theorem does not execute
the rational evaluator inside the natural-number algorithm. -/
theorem sequentialEvaluator_eq_numerator (alphabet : List (Word r Q))
    (ha : alphabet ≠ []) (vertices : List V) (indices : List (SeedIndex V E Δ))
    (default : Word r Q) (n : ℕ) (fixed : List (Word r Q)) :
    sequentialEvaluator alphabet (vertices.product vertices)
      (numberedPairSupport P slots indices) (numberedPairTerm P slots indices)
      (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ)) default n fixed =
      (sequentialNumerator P slots alphabet vertices indices default n fixed : ℚ) /
        (alphabet.length : ℚ) ^ (2 * (Δ + 1)) -
          pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ) := by
  have h := localEvaluator_eq_commonNumerator alphabet ha (vertices.product vertices)
    (numberedNaturalPairTerm P slots indices) (numberedPairSupport P slots indices)
    (2 * (Δ + 1)) (List.range' fixed.length n)
    (fun pair => (active_length_le _ _ List.nodup_range').trans
      (numberedPairSupport_card_le P slots indices pair))
    (decode default fixed) (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ))
  simpa only [sequentialEvaluator, sequentialNumerator, numberedPairNumerator,
    numberedNaturalPairTerm_cast] using h

omit [NeZero r] in
/-- All compared sequential scores have the same positive denominator and
  constant offset, so natural comparisons preserve even ties exactly. -/
theorem sequentialEvaluator_le_iff_numerator_le (alphabet : List (Word r Q))
    (ha : alphabet ≠ []) (vertices : List V) (indices : List (SeedIndex V E Δ))
    (default : Word r Q) (n₁ n₂ : ℕ) (fixed₁ fixed₂ : List (Word r Q)) :
    sequentialEvaluator alphabet (vertices.product vertices)
      (numberedPairSupport P slots indices) (numberedPairTerm P slots indices)
      (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ)) default n₁ fixed₁ ≤
    sequentialEvaluator alphabet (vertices.product vertices)
      (numberedPairSupport P slots indices) (numberedPairTerm P slots indices)
      (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ)) default n₂ fixed₂ ↔
      sequentialNumerator P slots alphabet vertices indices default n₁ fixed₁ ≤
        sequentialNumerator P slots alphabet vertices indices default n₂ fixed₂ := by
  have hpos : (0 : ℚ) < alphabet.length := by
    exact_mod_cast List.length_pos_iff.mpr ha
  rw [sequentialEvaluator_eq_numerator P slots alphabet ha,
    sequentialEvaluator_eq_numerator P slots alphabet ha, sub_le_sub_iff_right,
    div_le_div_iff_of_pos_right (pow_pos hpos _)]
  exact_mod_cast Iff.rfl

/-- The finite list of selected words. Every executed score is natural. -/
def naturalValues (a : Word r Q) (tail : List (Word r Q)) (vertices : List V)
    (indices : List (SeedIndex V E Δ)) : List (Word r Q) :=
  assignNat a tail (sequentialNumerator P slots (a :: tail) vertices indices a)
    indices.length []

omit [NeZero r] in
theorem naturalValues_eq_localAssign (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (indices : List (SeedIndex V E Δ)) :
    naturalValues P slots a tail vertices indices =
      localAssign a tail (vertices.product vertices) (numberedPairSupport P slots indices)
        (numberedPairTerm P slots indices)
        (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ)) a indices.length := by
  apply assignNat_eq_assignWithEvaluator
  intro n fixed x y
  exact sequentialEvaluator_le_iff_numerator_le P slots (a :: tail)
    (List.cons_ne_nil _ _) vertices indices a n n (x :: fixed) (y :: fixed)

/-- The actual deterministic assignment, computed by bounded local natural
counts and comparisons. The representation agrees with computedAssignment. -/
def naturalAssignment (a : Word r Q) (tail : List (Word r Q)) (vertices : List V)
    (indices : List (SeedIndex V E Δ)) : Assignment V E r Q Δ :=
  fun i => decode a (naturalValues P slots a tail vertices indices) (indexCode indices i)

omit [NeZero r] in
theorem naturalAssignment_eq_computedAssignment (a : Word r Q)
    (tail : List (Word r Q)) (vertices : List V) (indices : List (SeedIndex V E Δ)) :
    naturalAssignment P slots a tail vertices indices =
      computedAssignment P slots a tail vertices indices := by
  unfold naturalAssignment computedAssignment
  rw [naturalValues_eq_localAssign]

/-- The already-proved deviation bound transfers to the executable natural
comparison program through equality of the complete assignments. -/
theorem naturalAssignment_deviation_le (a : Word r Q) (tail : List (Word r Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (hvNodup : vertices.Nodup) (hvFull : ∀ v, v ∈ vertices)
    (indices : List (SeedIndex V E Δ)) (hiNodup : indices.Nodup)
    (hiFull : ∀ i, i ∈ indices) {k : ℕ} (hP : P.Bounded k Δ) :
    pairObjective P slots (naturalAssignment P slots a tail vertices indices) ≤
      (Fintype.card (UniversalType r Q Δ) : ℚ) *
        (1 + (Δ * k : ℕ)) * (Fintype.card V : ℚ) := by
  rw [naturalAssignment_eq_computedAssignment]
  exact computedAssignment_deviation_le P slots a tail haNodup haFull
    vertices hvNodup hvFull indices hiNodup hiFull hP

omit [NeZero r] in
theorem naturalAssignment_consistent (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (indices : List (SeedIndex V E Δ))
    (v : V) (e : Incident P v) :
    (assignmentType P slots (naturalAssignment P slots a tail vertices indices) v).slot
        (slots v e) =
      naturalAssignment P slots a tail vertices indices (.inl e.val) := by
  rw [naturalAssignment_eq_computedAssignment]
  exact computedAssignment_consistent P slots a tail vertices indices v e

/-- The concrete sequential numerator and its local collision-call counter. -/
def sequentialNumeratorCounted (alphabet : List (Word r Q)) (vertices : List V)
    (indices : List (SeedIndex V E Δ)) (default : Word r Q)
    (n : ℕ) (fixed : List (Word r Q)) : ℕ × ℕ :=
  commonNumeratorCounted alphabet (vertices.product vertices)
    (numberedNaturalPairTerm P slots indices) (numberedPairSupport P slots indices)
    (2 * (Δ + 1)) (List.range' fixed.length n) (decode default fixed)

omit [Fintype V] [NeZero r] in
theorem sequentialNumeratorCounted_value (alphabet : List (Word r Q))
    (vertices : List V) (indices : List (SeedIndex V E Δ)) (default : Word r Q)
    (n : ℕ) (fixed : List (Word r Q)) :
    (sequentialNumeratorCounted P slots alphabet vertices indices default n fixed).1 =
      sequentialNumerator P slots alphabet vertices indices default n fixed :=
  commonNumeratorCounted_value _ _ _ _ _ _ _

omit [NeZero r] in
theorem sequentialNumeratorCounted_calls (alphabet : List (Word r Q))
    (vertices : List V) (indices : List (SeedIndex V E Δ)) (default : Word r Q)
    (n : ℕ) (fixed : List (Word r Q)) :
    (sequentialNumeratorCounted P slots alphabet vertices indices default n fixed).2 =
      (SubexponentialSAT.LocalExpectation.sequentialEvaluatorCounted alphabet (vertices.product vertices)
        (numberedPairSupport P slots indices) (numberedPairTerm P slots indices)
        (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ)) default n fixed).2 := by
  rw [sequentialNumeratorCounted, commonNumeratorCounted_calls,
    SubexponentialSAT.LocalExpectation.sequentialEvaluatorCounted,
    SubexponentialSAT.LocalExpectation.localEvaluatorCounted_calls]

/-- The natural assignment program instrumented through the actual recursion. -/
def naturalAssignmentCounted (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (indices : List (SeedIndex V E Δ)) :
    Assignment V E r Q Δ × ℕ :=
  let result := assignWithCostNat a tail
    (sequentialNumeratorCounted P slots (a :: tail) vertices indices a) indices.length []
  (fun i => decode a result.1 (indexCode indices i), result.2)

omit [NeZero r] in
theorem naturalAssignmentCounted_eq (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (indices : List (SeedIndex V E Δ)) :
    naturalAssignmentCounted P slots a tail vertices indices =
      computedAssignmentCounted P slots a tail vertices indices := by
  have h := assignWithCostNat_eq a tail
    (sequentialNumeratorCounted P slots (a :: tail) vertices indices a)
    (SubexponentialSAT.LocalExpectation.sequentialEvaluatorCounted (a :: tail) (vertices.product vertices)
      (numberedPairSupport P slots indices) (numberedPairTerm P slots indices)
      (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ)) a)
    (by
      intro n fixed x y
      simpa only [SubexponentialSAT.LocalExpectation.sequentialEvaluatorCounted_value,
        sequentialNumeratorCounted_value] using
        sequentialEvaluator_le_iff_numerator_le P slots (a :: tail)
          (List.cons_ne_nil _ _) vertices indices a n n (x :: fixed) (y :: fixed))
    (sequentialNumeratorCounted_calls P slots (a :: tail) vertices indices a)
    indices.length []
  simp only [naturalAssignmentCounted, computedAssignmentCounted, h]

omit [NeZero r] in
theorem naturalAssignmentCounted_value (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (indices : List (SeedIndex V E Δ)) :
    (naturalAssignmentCounted P slots a tail vertices indices).1 =
      naturalAssignment P slots a tail vertices indices := by
  rw [naturalAssignmentCounted_eq, computedAssignmentCounted_value,
    naturalAssignment_eq_computedAssignment]

/-- The natural-score implementation performs the same polynomially bounded
number of local collision evaluations. This is not a Turing-machine cost claim. -/
theorem naturalAssignmentCounted_calls_uniform (a : Word r Q) (tail : List (Word r Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (hvNodup : vertices.Nodup) (hvFull : ∀ v, v ∈ vertices)
    (indices : List (SeedIndex V E Δ)) (hiNodup : indices.Nodup)
    (hiFull : ∀ i, i ∈ indices) {k : ℕ} (hP : P.Bounded k Δ) :
    (naturalAssignmentCounted P slots a tail vertices indices).2 ≤
      2 * (2 * Δ + 1) * (Fintype.card V) ^ 3 * (blockSize r Q Δ) ^ 3 := by
  rw [naturalAssignmentCounted_eq]
  exact computedAssignmentCounted_calls_uniform P slots a tail haNodup haFull
    vertices hvNodup hvFull indices hiNodup hiFull hP

/-- Fully explicit word and seed enumerations for the natural-score program.
Only the input's vertex and factor lists remain as enumeration inputs. -/
def enumeratedNaturalAssignment (vertices : List V) (factors : List E) :
    Assignment V E r Q Δ :=
  naturalAssignment P slots
    (AssignmentEnumeration.firstWord r Q (Nat.pos_of_neZero r))
    (AssignmentEnumeration.remainingWords r Q) vertices
    (AssignmentEnumeration.seedIndices vertices factors Δ)

theorem enumeratedNaturalAssignment_eq (vertices : List V) (factors : List E) :
    enumeratedNaturalAssignment (r := r) (Q := Q) P slots vertices factors =
      AssignmentEnumeration.enumeratedAssignment (r := r) (Q := Q) P slots vertices factors :=
  naturalAssignment_eq_computedAssignment P slots _ _ _ _

theorem enumeratedNaturalAssignment_deviation_le (vertices : List V) (factors : List E)
    (hvn : vertices.Nodup) (hvc : ∀ v, v ∈ vertices)
    (hen : factors.Nodup) (hec : ∀ e, e ∈ factors) {k : ℕ} (hP : P.Bounded k Δ) :
    pairObjective P slots
      (enumeratedNaturalAssignment (r := r) (Q := Q) P slots vertices factors) ≤
      (Fintype.card (UniversalType r Q Δ) : ℚ) *
        (1 + (Δ * k : ℕ)) * (Fintype.card V : ℚ) := by
  rw [enumeratedNaturalAssignment_eq]
  exact AssignmentEnumeration.enumeratedAssignment_deviation_le P slots
    vertices factors hvn hvc hen hec hP

end PairScores

end SubexponentialSAT.Subexp.NaturalAssignment

end OAI.Algorithms
