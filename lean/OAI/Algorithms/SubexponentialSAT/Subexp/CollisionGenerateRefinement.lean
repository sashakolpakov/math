import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionGenerateProgram
import OAI.Algorithms.SubexponentialSAT.SubexpTupleRefinement

namespace OAI.Algorithms

/-!
# The generated collision count is the padded pair count

The actual tuple generator may reverse record order. Its multiplicities,
the fixed-width word encoding, and the collision callback nevertheless give
exactly the successful-leaf count of the explicit padded completion tree.
-/

namespace SubexponentialSAT.Subexp.CollisionGenerateRefinement

open MulticolorTypes SlotAssignment SubexpTypeVariance

theorem vectors_eq_tuples {A : Type*} (alphabet : List A) (n : ℕ) :
    QuarticSearch.vectors alphabet n = CoefficientSearch.tuples alphabet n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [QuarticSearch.vectors, CoefficientSearch.tuples, ih]

theorem generated_word_perm {r Q : ℕ} (alphabet : List (Word r Q)) (n : ℕ) :
    (TupleProgram.powerRows (alphabet.map ReadPlan.encodeWord) n [[]]).Perm
      ((CoefficientSearch.tuples alphabet n).map fun v =>
        CollisionTupleProgram.tupleBytes (List.ofFn v)) := by
  have h := SubexpTupleRefinement.powerRows_empty_perm (alphabet.map ReadPlan.encodeWord) n
  rw [SubexpTupleRefinement.vectors_map, vectors_eq_tuples, List.map_map] at h
  simpa [SubexpTupleRefinement.tuplePayload, CollisionTupleProgram.tupleBytes,
    List.map_ofFn, Function.comp_def] using h

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {r Q Δ : ℕ} [NeZero r] (P : Factor.Pattern V E) (slots : SlotMap P Δ)

omit [Fintype V] [NeZero r] in
theorem leafBit_eq_plannedCollision (vertices : List V) (factors : List E)
    (default : Word r Q) (fixed candidate : List (Word r Q)) (remaining : List ℕ)
    (pair : V × V) :
    let current := ReadPlan.currentArray default
      (AssignmentEnumeration.seedIndices vertices factors Δ).length fixed
    CollisionTupleProgram.leafBit (CollisionTupleProgram.tupleBytes current) (ReadPlan.wordWidth r Q)
      (CollisionStreamProgram.completionPlan P slots vertices factors current.length remaining pair.1)
      (CollisionStreamProgram.completionPlan P slots vertices factors current.length remaining pair.2)
      (CollisionTupleProgram.tupleBytes candidate) =
        ReadPlan.plannedCollision P slots vertices factors default fixed remaining candidate pair := by
  dsimp only
  let current := ReadPlan.currentArray default
    (AssignmentEnumeration.seedIndices vertices factors Δ).length fixed
  have hrows : ∀ row ∈ current.map ReadPlan.encodeWord ++ candidate.map ReadPlan.encodeWord,
      row.length = ReadPlan.wordWidth r Q := by
    intro row hrow
    apply CollisionStreamProgram.completionRows_width current candidate row
    simpa [CollisionStreamProgram.completionRows] using hrow
  change CollisionTupleProgram.leafBit (CollisionTupleProgram.tupleBytes current) _ _ _ _ = _
  rw [CollisionTupleProgram.tupleBytes, CollisionTupleProgram.tupleBytes,
    CollisionTupleProgram.leafBit_eq_collision _ _ _ hrows, ← List.map_append]
  change decide (ReadPlan.partialEncoding P slots vertices factors current remaining candidate pair.1 =
    ReadPlan.partialEncoding P slots vertices factors current remaining candidate pair.2) =
      (ReadPlan.partialEncoding P slots vertices factors current remaining candidate pair.1 ==
        ReadPlan.partialEncoding P slots vertices factors current remaining candidate pair.2)
  apply Bool.eq_iff_iff.mpr
  simp

omit [Fintype V] [NeZero r] in
theorem generated_leaves_perm (alphabet : List (Word r Q)) (vertices : List V) (factors : List E)
    (default : Word r Q) (fixed : List (Word r Q)) (remaining : List ℕ)
    (depth : ℕ) (pair : V × V) :
    let current := ReadPlan.currentArray default
      (AssignmentEnumeration.seedIndices vertices factors Δ).length fixed
    (CollisionTupleProgram.streamed (CollisionTupleProgram.tupleBytes current) (ReadPlan.wordWidth r Q)
      (CollisionStreamProgram.completionPlan P slots vertices factors current.length remaining pair.1)
      (CollisionStreamProgram.completionPlan P slots vertices factors current.length remaining pair.2)
      (TupleProgram.powerRows (alphabet.map ReadPlan.encodeWord) depth [[]]) []).Perm
        ((CoefficientSearch.tuples alphabet depth).map fun v =>
          ReadPlan.plannedCollision P slots vertices factors default fixed remaining (List.ofFn v) pair) := by
  dsimp only
  let current := ReadPlan.currentArray default
    (AssignmentEnumeration.seedIndices vertices factors Δ).length fixed
  let test := CollisionTupleProgram.leafBit (CollisionTupleProgram.tupleBytes current)
    (ReadPlan.wordWidth r Q)
    (CollisionStreamProgram.completionPlan P slots vertices factors current.length remaining pair.1)
    (CollisionStreamProgram.completionPlan P slots vertices factors current.length remaining pair.2)
  have h := (generated_word_perm alphabet depth).map test
  have heq : ((CoefficientSearch.tuples alphabet depth).map
      (fun v => CollisionTupleProgram.tupleBytes (List.ofFn v))).map test =
      (CoefficientSearch.tuples alphabet depth).map (fun v =>
        ReadPlan.plannedCollision P slots vertices factors default fixed remaining (List.ofFn v) pair) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro v _
    exact leafBit_eq_plannedCollision P slots vertices factors default fixed (List.ofFn v) remaining pair
  rw [heq] at h
  have hrev := List.reverse_perm
    ((TupleProgram.powerRows (alphabet.map ReadPlan.encodeWord) depth [[]]).map test)
  simpa only [CollisionTupleProgram.streamed_eq_reverse_map, List.append_nil] using hrev.trans h

def generatedPairLeaves (alphabet : List (Word r Q)) (vertices : List V) (factors : List E)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ) (pair : V × V) : List Bool :=
  let current := ReadPlan.currentArray default
    (AssignmentEnumeration.seedIndices vertices factors Δ).length fixed
  let remaining := ReadPlan.remainingPlan P slots vertices factors pair fixed.length remainingCount
  CollisionTupleProgram.streamed (CollisionTupleProgram.tupleBytes current) (ReadPlan.wordWidth r Q)
    (CollisionStreamProgram.completionPlan P slots vertices factors current.length remaining pair.1)
    (CollisionStreamProgram.completionPlan P slots vertices factors current.length remaining pair.2)
    (TupleProgram.powerRows (alphabet.map ReadPlan.encodeWord) (2 * (Δ + 1)) [[]]) []

omit [Fintype V] [NeZero r] in
theorem generated_pair_perm (alphabet : List (Word r Q)) (vertices : List V) (factors : List E)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ) (pair : V × V) :
    (generatedPairLeaves P slots alphabet vertices factors default fixed remainingCount pair).Perm
      (ReadPlan.plannedPairLeaves P slots alphabet vertices factors default fixed remainingCount pair) := by
  let remaining := ReadPlan.remainingPlan P slots vertices factors pair fixed.length remainingCount
  have hlen : (PaddedCompletion.paddedIndices remaining (2 * (Δ + 1))).length = 2 * (Δ + 1) :=
    PaddedCompletion.paddedIndices_length _ _
      (ReadPlan.remainingPlan_length_le P slots vertices factors pair fixed.length remainingCount)
  have h := generated_leaves_perm P slots alphabet vertices factors default fixed remaining
    (2 * (Δ + 1)) pair
  change (generatedPairLeaves P slots alphabet vertices factors default fixed remainingCount pair).Perm
    ((CoefficientSearch.tuples alphabet
      (PaddedCompletion.paddedIndices remaining (2 * (Δ + 1))).length).map fun v =>
      ReadPlan.plannedCollision P slots vertices factors default fixed remaining (List.ofFn v) pair)
  rw [hlen]
  exact h

omit [Fintype V] [NeZero r] in
/-- Reversal of the actual generated records changes neither multiplicity nor
the successful-leaf count used by the subsequent unary tally. -/
theorem generated_pair_trueCount (alphabet : List (Word r Q)) (vertices : List V) (factors : List E)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ) (pair : V × V) :
    PaddedCompletion.trueCount
      (generatedPairLeaves P slots alphabet vertices factors default fixed remainingCount pair) =
    PaddedCompletion.trueCount
      (ReadPlan.plannedPairLeaves P slots alphabet vertices factors default fixed remainingCount pair) :=
  ((generated_pair_perm P slots alphabet vertices factors default fixed remainingCount pair).filter id).length_eq

omit [Fintype V] [NeZero r] in
theorem generated_pair_length (alphabet : List (Word r Q)) (vertices : List V) (factors : List E)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ) (pair : V × V) :
    (generatedPairLeaves P slots alphabet vertices factors default fixed remainingCount pair).length =
      alphabet.length ^ (2 * (Δ + 1)) := by
  rw [(generated_pair_perm P slots alphabet vertices factors default fixed remainingCount pair).length_eq]
  exact ReadPlan.plannedPairLeaves_length P slots alphabet vertices factors default fixed remainingCount pair

end SubexponentialSAT.Subexp.CollisionGenerateRefinement

end OAI.Algorithms
