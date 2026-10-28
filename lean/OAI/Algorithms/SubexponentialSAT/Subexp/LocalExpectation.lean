import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.LocalExpectation
import OAI.Algorithms.SubexponentialSAT.SubexpTypeVariance

namespace OAI.Algorithms

/-!
# Uniform multi-color conditional expectation

All parameters remain visible. The local evaluator enumerates only each pair's
read support, and its total evaluation bound is a fixed polynomial in the
number of chunks and universal types. Natural completion counts also give a
common-denominator representation for the rational conditional scores.
-/

namespace SubexponentialSAT.Subexp.LocalExpectation

open SubexponentialSAT.LocalExpectation SubexponentialSAT.ConditionalExpectation
open scoped BigOperators

variable {I W J : Type*} [DecidableEq I]

/-- Unnormalized finite completion count. Its terminal function can be a local
zero/one collision indicator. -/
def completionCount (alphabet : List W) (f : (I → W) → ℕ) :
    List I → (I → W) → ℕ
  | [], ω => f ω
  | i :: remaining, ω =>
      (alphabet.map (fun w => completionCount alphabet f remaining (Function.update ω i w))).sum

private theorem sum_map_le (xs : List W) (f : W → ℕ) (B : ℕ) (hf : ∀ w, f w ≤ B) :
    (xs.map f).sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons w xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        _ ≤ B + xs.length * B := Nat.add_le_add (hf w) ih
        _ = _ := by ring

theorem completionCount_le (alphabet : List W) (f : (I → W) → ℕ)
    (hf : ∀ ω, f ω ≤ 1) (remaining : List I) (ω : I → W) :
    completionCount alphabet f remaining ω ≤ alphabet.length ^ remaining.length := by
  induction remaining generalizing ω with
  | nil => exact hf ω
  | cons i remaining ih =>
      simp only [completionCount, List.length_cons]
      calc
        _ ≤ alphabet.length * alphabet.length ^ remaining.length :=
          sum_map_le alphabet _ _ (fun w => ih _)
        _ = _ := by rw [pow_succ]; exact Nat.mul_comm _ _

private theorem cast_sum_map (xs : List W) (f : W → ℕ) :
    (((xs.map f).sum : ℕ) : ℚ) = (xs.map (fun w => (f w : ℚ))).sum := by
  induction xs with
  | nil => simp
  | cons w xs ih => simp [ih]

private theorem sum_map_div (xs : List W) (f : W → ℚ) (d : ℚ) :
    (xs.map (fun w => f w / d)).sum = (xs.map f).sum / d := by
  induction xs with
  | nil => simp
  | cons w xs ih => simp [ih, add_div]

/-- Exact numerator and denominator for an exhaustive local average. -/
theorem wordExpectation_eq_completionCount (alphabet : List W) (f : (I → W) → ℕ)
    (remaining : List I) (ω : I → W) :
    wordExpectation alphabet (fun η => (f η : ℚ)) remaining ω =
      (completionCount alphabet f remaining ω : ℚ) /
        (alphabet.length : ℚ) ^ remaining.length := by
  induction remaining generalizing ω with
  | nil => simp [wordExpectation, completionCount]
  | cons i remaining ih =>
      simp only [wordExpectation]
      simp_rw [ih]
      unfold mean
      rw [sum_map_div, ← cast_sum_map]
      simp only [completionCount, List.length_cons, pow_succ, div_div, mul_comm]

/-- A local numerator scaled to a common power of the word alphabet size. -/
def scaledCount (alphabet : List W) (f : (I → W) → ℕ) (support : Finset I)
    (S : ℕ) (remaining : List I) (ω : I → W) : ℕ :=
  alphabet.length ^ (S - (active support remaining).length) *
    completionCount alphabet f (active support remaining) ω

theorem scaledCount_le (alphabet : List W) (f : (I → W) → ℕ)
    (hf : ∀ ω, f ω ≤ 1) (support : Finset I) (S : ℕ)
    (remaining : List I) (hS : (active support remaining).length ≤ S) (ω : I → W) :
    scaledCount alphabet f support S remaining ω ≤ alphabet.length ^ S := by
  unfold scaledCount
  calc
    _ ≤ alphabet.length ^ (S - (active support remaining).length) *
        alphabet.length ^ (active support remaining).length :=
      Nat.mul_le_mul_left _ (completionCount_le alphabet f hf _ ω)
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hS]

theorem local_average_eq_scaledCount (alphabet : List W) (ha : alphabet ≠ [])
    (f : (I → W) → ℕ) (support : Finset I) (S : ℕ)
    (remaining : List I) (hS : (active support remaining).length ≤ S) (ω : I → W) :
    wordExpectation alphabet (fun η => (f η : ℚ)) (active support remaining) ω =
      (scaledCount alphabet f support S remaining ω : ℚ) / (alphabet.length : ℚ) ^ S := by
  rw [wordExpectation_eq_completionCount]
  have hq : (alphabet.length : ℚ) ≠ 0 := by
    exact_mod_cast (List.length_pos_iff.mpr ha).ne'
  have hp : (alphabet.length : ℚ) ^ S =
      (alphabet.length : ℚ) ^ (S - (active support remaining).length) *
        (alphabet.length : ℚ) ^ (active support remaining).length := by
    rw [← pow_add, Nat.sub_add_cancel hS]
  simp only [scaledCount, Nat.cast_mul, Nat.cast_pow, hp]
  exact (mul_div_mul_left _ _ (pow_ne_zero _ hq)).symm

/-- Natural common numerator for a sum of bounded-support local indicators. -/
def commonNumerator (alphabet : List W) (terms : List J)
    (f : J → (I → W) → ℕ) (support : J → Finset I) (S : ℕ)
    (remaining : List I) (ω : I → W) : ℕ :=
  (terms.map (fun j => scaledCount alphabet (f j) (support j) S remaining ω)).sum

theorem commonNumerator_le (alphabet : List W) (terms : List J)
    (f : J → (I → W) → ℕ) (hf : ∀ j ω, f j ω ≤ 1)
    (support : J → Finset I) (S : ℕ) (remaining : List I)
    (hS : ∀ j, (active (support j) remaining).length ≤ S) (ω : I → W) :
    commonNumerator alphabet terms f support S remaining ω ≤
      terms.length * alphabet.length ^ S :=
  sum_map_le terms _ _ (fun j => scaledCount_le alphabet (f j) (hf j) (support j) S remaining (hS j) ω)

/-- The common numerator represents the actual rational local evaluator,
including its constant offset. -/
theorem localEvaluator_eq_commonNumerator (alphabet : List W) (ha : alphabet ≠ [])
    (terms : List J) (f : J → (I → W) → ℕ) (support : J → Finset I) (S : ℕ)
    (remaining : List I) (hS : ∀ j, (active (support j) remaining).length ≤ S)
    (ω : I → W) (offset : ℚ) :
    localEvaluator alphabet terms support (fun j η => (f j η : ℚ)) offset remaining ω =
      (commonNumerator alphabet terms f support S remaining ω : ℚ) /
        (alphabet.length : ℚ) ^ S - offset := by
  unfold localEvaluator commonNumerator
  simp_rw [local_average_eq_scaledCount alphabet ha _ _ S remaining (hS _) ω]
  rw [sum_map_div, cast_sum_map]

section PairObjective

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpTypeVariance SubexponentialSAT.SlotAssignment

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (P : SubexponentialSAT.Factor.Pattern V E) {r Q Δ : ℕ} [NeZero r] (slots : SlotMap P Δ)

private theorem sum_enumeration {K : Type*} [DecidableEq K] [Fintype K]
    (xs : List K) (hn : xs.Nodup) (hc : ∀ x, x ∈ xs) (f : K → ℚ) :
    (xs.map f).sum = ∑ x, f x := by
  rw [← List.sum_toFinset f hn]
  have h : xs.toFinset = Finset.univ := by ext x; simp [hc x]
  rw [h]

private theorem sum_product {A B : Type*} (xs : List A) (ys : List B)
    (f : A × B → ℚ) :
    ((xs.product ys).map f).sum =
      (xs.map (fun x => (ys.map (fun y => f (x, y))).sum)).sum := by
  induction xs with
  | nil => simp [List.product]
  | cons x xs ih =>
      change (List.map f ((ys.map (fun y => (x, y))) ++ xs.product ys)).sum = _
      simp [List.map_map, Function.comp_def, ih]

private theorem list_product_length {A B : Type*} (xs : List A) (ys : List B) :
    (xs.product ys).length = xs.length * ys.length := List.length_product xs ys

/-- The squared type-count potential from Section 5.4. -/
def pairObjective (ω : Assignment V E r Q Δ) : ℚ :=
  ∑ u : UniversalType r Q Δ,
    ((SubexponentialSAT.Variance.typeCount (assignmentType P slots) u ω : ℚ) -
      (Fintype.card V : ℚ) / (Fintype.card (UniversalType r Q Δ) : ℚ)) ^ 2

def pairTerm (pair : V × V) (ω : Assignment V E r Q Δ) : ℚ :=
  pairCollision P slots ω pair.1 pair.2

def pairOffset : ℚ :=
  (Fintype.card V : ℚ) ^ 2 / (Fintype.card (UniversalType r Q Δ) : ℚ)

omit [Fintype V] [NeZero r] in
theorem pairTerm_dependsOn (pair : V × V) :
    DependsOn (pairSupport P slots pair.1 pair.2) (pairTerm (r := r) (Q := Q) P slots pair) := by
  intro ω ω' h
  exact pairCollision_congr P slots ω ω' pair.1 pair.2 h

omit [DecidableEq E] in
theorem objective_pair_eq (vertices : List V) (hn : vertices.Nodup)
    (hc : ∀ v, v ∈ vertices) (ω : Assignment V E r Q Δ) :
    objective (vertices.product vertices) (pairTerm P slots) (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ)) ω =
      pairObjective P slots ω := by
  unfold objective pairObjective
  rw [assignment_deviation_eq_collisions]
  unfold pairOffset
  congr 1
  rw [sum_product, sum_enumeration vertices hn hc]
  apply Finset.sum_congr rfl
  intro v _
  exact sum_enumeration vertices hn hc (fun w => pairCollision P slots ω v w)

/-- The actual local-pair evaluator on the manuscript's factor/head/padding
word variables. Only the union of the two read supports is enumerated. -/
def pairEvaluator (alphabet : List (Word r Q)) (vertices : List V)
    (remaining : List (SeedIndex V E Δ)) (ω : Assignment V E r Q Δ) : ℚ :=
  localEvaluator alphabet (vertices.product vertices)
    (fun pair => pairSupport P slots pair.1 pair.2) (pairTerm P slots)
    (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ)) remaining ω

theorem pairEvaluator_eq (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (vertices : List V) (hn : vertices.Nodup) (hc : ∀ v, v ∈ vertices)
    (remaining : List (SeedIndex V E Δ)) (ω : Assignment V E r Q Δ) :
    pairEvaluator P slots alphabet vertices remaining ω =
      wordExpectation alphabet (pairObjective P slots) remaining ω := by
  unfold pairEvaluator
  rw [localEvaluator_eq alphabet ha _ _ _ (pairTerm_dependsOn P slots)]
  have h : objective (vertices.product vertices) (pairTerm (r := r) (Q := Q) P slots)
      (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ)) = pairObjective (r := r) (Q := Q) P slots := by
    funext η
    exact objective_pair_eq P slots vertices hn hc η
  rw [h]

omit [NeZero r] in
/-- The evaluator makes at most `D² q^(2(Δ+1))` local collision calls for a
vertex enumeration of length `D`. This bound is uniform over partial assignments. -/
theorem pairEvaluator_calls_le (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (vertices : List V) (remaining : List (SeedIndex V E Δ)) (hr : remaining.Nodup)
    (ω : Assignment V E r Q Δ) :
    (localEvaluatorCounted alphabet (vertices.product vertices)
      (fun pair => pairSupport P slots pair.1 pair.2) (pairTerm P slots)
      (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ)) remaining ω).2 ≤
      vertices.length ^ 2 * alphabet.length ^ (2 * (Δ + 1)) := by
  simpa only [list_product_length, pow_two] using
    localEvaluatorCounted_calls_le alphabet ha (vertices.product vertices)
      (fun pair => pairSupport P slots pair.1 pair.2) (pairTerm P slots)
      (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ)) remaining hr ω (2 * (Δ + 1))
      (fun pair => pairSupport_card_le P slots pair.1 pair.2)

/-- Numbered local support from an explicit list of independent word indices. -/
def numberedPairSupport (indices : List (SeedIndex V E Δ)) (pair : V × V) : Finset ℕ :=
  (pairSupport P slots pair.1 pair.2).image (fun i => indexCode indices i)

def numberedPairTerm (indices : List (SeedIndex V E Δ)) (pair : V × V) :
    (ℕ → Word r Q) → ℚ :=
  reindexTerm (fun i => indexCode indices i) (pairTerm P slots pair)

omit [Fintype V] in
omit [NeZero r] in
theorem numberedPairTerm_dependsOn (indices : List (SeedIndex V E Δ)) (pair : V × V) :
    DependsOn (numberedPairSupport P slots indices pair)
      (numberedPairTerm (r := r) (Q := Q) P slots indices pair) :=
  reindexTerm_dependsOn _ _ _ (pairTerm_dependsOn P slots pair)

omit [Fintype V] in
theorem numberedPairSupport_card_le (indices : List (SeedIndex V E Δ)) (pair : V × V) :
    (numberedPairSupport P slots indices pair).card ≤ 2 * (Δ + 1) :=
  (Finset.card_image_le).trans (pairSupport_card_le P slots pair.1 pair.2)

/-- A concrete, terminating deterministic word assignment using the efficient
local-pair conditional evaluator at every choice. -/
def computedAssignment (a : Word r Q) (tail : List (Word r Q)) (vertices : List V)
    (indices : List (SeedIndex V E Δ)) : Assignment V E r Q Δ :=
  let values := localAssign a tail (vertices.product vertices)
    (numberedPairSupport P slots indices) (numberedPairTerm P slots indices)
    (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ)) a indices.length
  fun i => decode a values (indexCode indices i)

theorem computedAssignment_le_initial (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (hn : vertices.Nodup) (hc : ∀ v, v ∈ vertices)
    (indices : List (SeedIndex V E Δ)) :
    pairObjective P slots (computedAssignment P slots a tail vertices indices) ≤
      sequentialEvaluator (a :: tail) (vertices.product vertices)
        (numberedPairSupport P slots indices) (numberedPairTerm P slots indices)
        (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ)) a indices.length [] := by
  have h := localAssign_le_initial a tail (vertices.product vertices)
    (numberedPairSupport P slots indices) (numberedPairTerm P slots indices)
    (numberedPairTerm_dependsOn P slots indices) (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ)) a indices.length
  convert h using 1
  symm
  exact objective_pair_eq P slots vertices hn hc _

/-- The executable local-pair construction satisfies the manuscript's
deviation bound. All enumerations are explicit algorithm inputs. -/
theorem computedAssignment_deviation_le (a : Word r Q) (tail : List (Word r Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (hvNodup : vertices.Nodup) (hvFull : ∀ v, v ∈ vertices)
    (indices : List (SeedIndex V E Δ)) (hiNodup : indices.Nodup)
    (hiFull : ∀ i, i ∈ indices) {k : ℕ} (hP : P.Bounded k Δ) :
    pairObjective P slots (computedAssignment P slots a tail vertices indices) ≤
      (Fintype.card (UniversalType r Q Δ) : ℚ) *
        (1 + (Δ * k : ℕ)) * (Fintype.card V : ℚ) := by
  calc
    _ ≤ sequentialEvaluator (a :: tail) (vertices.product vertices)
        (numberedPairSupport P slots indices) (numberedPairTerm P slots indices)
        (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ)) a indices.length [] :=
      computedAssignment_le_initial P slots a tail vertices hvNodup hvFull indices
    _ = SubexponentialSAT.Variance.mean SubexponentialSAT.Variance.uniformWeight
        (objective (vertices.product vertices) (pairTerm (r := r) (Q := Q) P slots)
          (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ))) := by
      exact initialEvaluator_reindex_uniform (a :: tail) (List.cons_ne_nil _ _) haNodup haFull
        (vertices.product vertices) (fun pair => pairSupport P slots pair.1 pair.2)
        (pairTerm (r := r) (Q := Q) P slots) (pairTerm_dependsOn P slots)
        (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ)) a indices hiNodup hiFull
    _ = SubexponentialSAT.Variance.mean SubexponentialSAT.Variance.uniformWeight (pairObjective (r := r) (Q := Q) P slots) := by
      apply congrArg (SubexponentialSAT.Variance.mean SubexponentialSAT.Variance.uniformWeight)
      funext ω
      exact objective_pair_eq P slots vertices hvNodup hvFull ω
    _ ≤ _ := mean_squared_deviation_le P slots hP

omit [NeZero r] in
/-- A shared factor receives one word at all of its incidences in the computed
assignment, so the derandomization preserves the required slot consistency. -/
theorem computedAssignment_consistent (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (indices : List (SeedIndex V E Δ))
    (v : V) (e : Incident P v) :
    (assignmentType P slots (computedAssignment P slots a tail vertices indices) v).slot
        (slots v e) =
      computedAssignment P slots a tail vertices indices (.inl e.val) := by
  rw [assignmentType_eq_typeFromWords, SubexponentialSAT.MulticolorTypes.typeFromWords_incidence]

omit [NeZero r] in
/-- The same concrete assignment, instrumented to count local collision calls. -/
def computedAssignmentCounted (a : Word r Q) (tail : List (Word r Q)) (vertices : List V)
    (indices : List (SeedIndex V E Δ)) : Assignment V E r Q Δ × ℕ :=
  let result := assignWithCost a tail
    (sequentialEvaluatorCounted (a :: tail) (vertices.product vertices)
      (numberedPairSupport P slots indices) (numberedPairTerm P slots indices)
      (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ)) a) indices.length []
  (fun i => decode a result.1 (indexCode indices i), result.2)

omit [NeZero r] in
theorem computedAssignmentCounted_value (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (indices : List (SeedIndex V E Δ)) :
    (computedAssignmentCounted P slots a tail vertices indices).1 =
      computedAssignment P slots a tail vertices indices := by
  simp only [computedAssignmentCounted, computedAssignment, localAssign,
    assignWithCost_value, sequentialEvaluatorCounted_value]

omit [NeZero r] in
/-- Whole-search bound: the actual instrumented program makes at most
`M * 2(q-1) * D² * q^(2(Δ+1))` local collision evaluations. -/
theorem computedAssignmentCounted_calls_le (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (indices : List (SeedIndex V E Δ)) :
    (computedAssignmentCounted P slots a tail vertices indices).2 ≤
      indices.length * (2 * tail.length *
        (vertices.length ^ 2 * (a :: tail).length ^ (2 * (Δ + 1)))) := by
  apply assignWithCost_calls_le
  intro n fixed
  simpa only [list_product_length, pow_two] using
    sequentialEvaluatorCounted_calls_le (a :: tail) (List.cons_ne_nil _ _)
      (vertices.product vertices) (numberedPairSupport P slots indices)
      (numberedPairTerm P slots indices) (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ))
      a n fixed (2 * (Δ + 1)) (numberedPairSupport_card_le P slots indices)

private theorem enumeration_length {K : Type*} [DecidableEq K] [Fintype K]
    (xs : List K) (hn : xs.Nodup) (hc : ∀ x, x ∈ xs) : xs.length = Fintype.card K := by
  rw [← List.toFinset_card_of_nodup hn]
  have h : xs.toFinset = Finset.univ := by ext x; simp [hc x]
  rw [h, Finset.card_univ]

/-- The explicit seed representation includes factor words, heads, and all
padding slots. Its length is still linear in the number of chunks. -/
theorem indices_length_le (indices : List (SeedIndex V E Δ))
    (hn : indices.Nodup) (hc : ∀ i, i ∈ indices) {k : ℕ} (hP : P.Bounded k Δ) :
    indices.length ≤ (2 * Δ + 1) * Fintype.card V := by
  rw [enumeration_length indices hn hc]
  simp only [SeedIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have h := SubexponentialSAT.Incidence.bounded_card_factors_le P k Δ hP
  nlinarith

omit [NeZero r] in
/-- A polynomial bound in the input chunk count for the fully instrumented
local-pair search. The leading factor depends only on the fixed alphabet and Δ.
Arithmetic bit costs and list-processing costs are not asserted to be unit cost. -/
theorem computedAssignmentCounted_calls_polynomial (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (hvNodup : vertices.Nodup) (hvFull : ∀ v, v ∈ vertices)
    (indices : List (SeedIndex V E Δ)) (hiNodup : indices.Nodup)
    (hiFull : ∀ i, i ∈ indices) {k : ℕ} (hP : P.Bounded k Δ) :
    (computedAssignmentCounted P slots a tail vertices indices).2 ≤
      ((2 * Δ + 1) * (2 * tail.length) * (a :: tail).length ^ (2 * (Δ + 1))) *
        (Fintype.card V) ^ 3 := by
  calc
    _ ≤ indices.length * (2 * tail.length *
        (vertices.length ^ 2 * (a :: tail).length ^ (2 * (Δ + 1)))) :=
      computedAssignmentCounted_calls_le P slots a tail vertices indices
    _ = indices.length * (2 * tail.length *
        ((Fintype.card V) ^ 2 * (a :: tail).length ^ (2 * (Δ + 1)))) := by
      rw [enumeration_length vertices hvNodup hvFull]
    _ ≤ ((2 * Δ + 1) * Fintype.card V) * (2 * tail.length *
        ((Fintype.card V) ^ 2 * (a :: tail).length ^ (2 * (Δ + 1)))) :=
      Nat.mul_le_mul_right _ (indices_length_le P indices hiNodup hiFull hP)
    _ = _ := by ring

omit [NeZero r] in
/-- The support-completion power is exactly the square of the universal block
size, even when every displayed parameter grows. -/
theorem alphabet_pair_power (alphabet : List (Word r Q))
    (hn : alphabet.Nodup) (hc : ∀ w, w ∈ alphabet) :
    alphabet.length ^ (2 * (Δ + 1)) = (blockSize r Q Δ) ^ 2 := by
  rw [enumeration_length alphabet hn hc, card_word]
  simp only [blockSize, ← pow_mul]
  congr 1
  ring

/-- Uniform fixed-degree polynomial bound for the whole local-word search.
In particular no exponent of D or N depends on r,Q,Δ, or k. -/
theorem computedAssignmentCounted_calls_uniform (a : Word r Q) (tail : List (Word r Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (hvNodup : vertices.Nodup) (hvFull : ∀ v, v ∈ vertices)
    (indices : List (SeedIndex V E Δ)) (hiNodup : indices.Nodup)
    (hiFull : ∀ i, i ∈ indices) {k : ℕ} (hP : P.Bounded k Δ) :
    (computedAssignmentCounted P slots a tail vertices indices).2 ≤
      2 * (2 * Δ + 1) * (Fintype.card V) ^ 3 * (blockSize r Q Δ) ^ 3 := by
  have hpower := alphabet_pair_power (Δ := Δ) (a :: tail) haNodup haFull
  have hlength : (a :: tail).length = r ^ Q := by
    rw [enumeration_length (a :: tail) haNodup haFull, card_word]
  have htail : tail.length ≤ blockSize r Q Δ := by
    calc
      tail.length ≤ (a :: tail).length := by simp
      _ = r ^ Q := hlength
      _ ≤ blockSize r Q Δ := word_choices_le_type_choices
  calc
    _ ≤ ((2 * Δ + 1) * (2 * tail.length) *
        (a :: tail).length ^ (2 * (Δ + 1))) * (Fintype.card V) ^ 3 :=
      computedAssignmentCounted_calls_polynomial P slots a tail vertices hvNodup hvFull
        indices hiNodup hiFull hP
    _ = (2 * (2 * Δ + 1) * (Fintype.card V) ^ 3 * (blockSize r Q Δ) ^ 2) *
        tail.length := by rw [hpower]; ring
    _ ≤ (2 * (2 * Δ + 1) * (Fintype.card V) ^ 3 * (blockSize r Q Δ) ^ 2) *
        blockSize r Q Δ := Nat.mul_le_mul_left _ htail
    _ = _ := by ring

/-- The local collision as a natural zero/one function. -/
def naturalPairTerm (pair : V × V) (ω : Assignment V E r Q Δ) : ℕ :=
  if assignmentType P slots ω pair.1 = assignmentType P slots ω pair.2 then 1 else 0

omit [Fintype V] [NeZero r] in
omit [DecidableEq E] in
theorem naturalPairTerm_cast (pair : V × V) (ω : Assignment V E r Q Δ) :
    (naturalPairTerm P slots pair ω : ℚ) = pairTerm P slots pair ω := by
  simp only [naturalPairTerm, pairTerm, pairCollision]
  split_ifs <;> rfl

omit [Fintype V] [NeZero r] in
omit [DecidableEq E] in
theorem naturalPairTerm_le (pair : V × V) (ω : Assignment V E r Q Δ) :
    naturalPairTerm P slots pair ω ≤ 1 := by
  unfold naturalPairTerm
  split_ifs <;> omega

/-- A bounded natural common numerator for all pair terms of the conditional
objective. Its common denominator is N². -/
def pairNumerator (alphabet : List (Word r Q)) (vertices : List V)
    (remaining : List (SeedIndex V E Δ)) (ω : Assignment V E r Q Δ) : ℕ :=
  commonNumerator alphabet (vertices.product vertices) (naturalPairTerm P slots)
    (fun pair => pairSupport P slots pair.1 pair.2) (2 * (Δ + 1)) remaining ω

omit [Fintype V] [NeZero r] in
theorem pairNumerator_le (alphabet : List (Word r Q))
    (haNodup : alphabet.Nodup) (haFull : ∀ w, w ∈ alphabet)
    (vertices : List V) (remaining : List (SeedIndex V E Δ)) (hr : remaining.Nodup)
    (ω : Assignment V E r Q Δ) :
    pairNumerator P slots alphabet vertices remaining ω ≤
      vertices.length ^ 2 * (blockSize r Q Δ) ^ 2 := by
  have h := commonNumerator_le alphabet (vertices.product vertices) (naturalPairTerm P slots)
    (naturalPairTerm_le P slots) (fun pair => pairSupport P slots pair.1 pair.2)
    (2 * (Δ + 1)) remaining
    (fun pair => (active_length_le _ _ hr).trans (pairSupport_card_le P slots pair.1 pair.2)) ω
  simpa only [pairNumerator, list_product_length, ← pow_two,
    alphabet_pair_power alphabet haNodup haFull] using h

omit [NeZero r] in
/-- Every conditional score has the same displayed denominator, and the
numerator above is bounded by D²N². -/
theorem pairEvaluator_eq_numerator (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (haNodup : alphabet.Nodup) (haFull : ∀ w, w ∈ alphabet)
    (vertices : List V) (remaining : List (SeedIndex V E Δ)) (hr : remaining.Nodup)
    (ω : Assignment V E r Q Δ) :
    pairEvaluator P slots alphabet vertices remaining ω =
      (pairNumerator P slots alphabet vertices remaining ω : ℚ) /
        ((blockSize r Q Δ : ℕ) : ℚ) ^ 2 - pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ) := by
  have h := localEvaluator_eq_commonNumerator alphabet ha (vertices.product vertices)
    (naturalPairTerm P slots) (fun pair => pairSupport P slots pair.1 pair.2)
    (2 * (Δ + 1)) remaining
    (fun pair => (active_length_le _ _ hr).trans (pairSupport_card_le P slots pair.1 pair.2))
    ω (pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ))
  have hp : (alphabet.length : ℚ) ^ (2 * (Δ + 1)) =
      ((blockSize r Q Δ : ℕ) : ℚ) ^ 2 := by
    exact_mod_cast alphabet_pair_power (Δ := Δ) alphabet haNodup haFull
  simpa only [pairEvaluator, pairNumerator, naturalPairTerm_cast, hp] using h

/-- Comparing conditional scores requires only comparing bounded natural
numerators. The offset and positive common denominator cancel exactly. -/
theorem pairEvaluator_le_iff_numerator_le (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (haNodup : alphabet.Nodup) (haFull : ∀ w, w ∈ alphabet) (vertices : List V)
    (remaining₁ remaining₂ : List (SeedIndex V E Δ))
    (hr₁ : remaining₁.Nodup) (hr₂ : remaining₂.Nodup)
    (ω₁ ω₂ : Assignment V E r Q Δ) :
    pairEvaluator P slots alphabet vertices remaining₁ ω₁ ≤
        pairEvaluator P slots alphabet vertices remaining₂ ω₂ ↔
      pairNumerator P slots alphabet vertices remaining₁ ω₁ ≤
        pairNumerator P slots alphabet vertices remaining₂ ω₂ := by
  have hN : (0 : ℚ) < ((blockSize r Q Δ : ℕ) : ℚ) := by
    exact_mod_cast (pow_pos (Nat.pos_of_ne_zero (NeZero.ne r)) (Q * (Δ + 1)))
  rw [pairEvaluator_eq_numerator P slots alphabet ha haNodup haFull vertices remaining₁ hr₁ ω₁,
    pairEvaluator_eq_numerator P slots alphabet ha haNodup haFull vertices remaining₂ hr₂ ω₂,
    sub_le_sub_iff_right, div_le_div_iff_of_pos_right (pow_pos hN 2)]
  exact_mod_cast Iff.rfl

private theorem size_square_product_le (D N : ℕ) :
    (D ^ 2 * N ^ 2).size ≤ 2 * D.size + 2 * N.size + 1 := by
  have hD : D ≤ 2 ^ D.size := (Nat.lt_size_self D).le
  have hN : N ≤ 2 ^ N.size := (Nat.lt_size_self N).le
  have hDs : D ^ 2 ≤ (2 ^ D.size) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hD hD
  have hNs : N ^ 2 ≤ (2 ^ N.size) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hN hN
  apply Nat.size_le.mpr
  have hprod := Nat.mul_le_mul hDs hNs
  have hp : (2 ^ D.size) ^ 2 * (2 ^ N.size) ^ 2 = 2 ^ (2 * D.size + 2 * N.size) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [hp] at hprod
  exact hprod.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

omit [Fintype V] [NeZero r] in
/-- Explicit logarithmic bit-size bound on every natural score numerator. -/
theorem pairNumerator_bitSize_le (alphabet : List (Word r Q))
    (haNodup : alphabet.Nodup) (haFull : ∀ w, w ∈ alphabet)
    (vertices : List V) (remaining : List (SeedIndex V E Δ)) (hr : remaining.Nodup)
    (ω : Assignment V E r Q Δ) :
    (pairNumerator P slots alphabet vertices remaining ω).size ≤
      2 * vertices.length.size + 2 * (blockSize r Q Δ).size + 1 :=
  (Nat.size_le_size (pairNumerator_le P slots alphabet haNodup haFull vertices remaining hr ω)).trans
    (size_square_product_le vertices.length (blockSize r Q Δ))

end PairObjective

end SubexponentialSAT.Subexp.LocalExpectation

end OAI.Algorithms
