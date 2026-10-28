import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCompletion
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionGenerateRefinement
import OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreRefinement

namespace OAI.Algorithms

/-! Runtime-generated incidence collision leaves, using actual two-word read plans. -/
namespace SubexponentialSAT.SqrtLog.Packing
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.Subexp

section Plans
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

def incidenceReadPlan (indices : List (V ⊕ E)) (i : I) : List ℕ :=
  [indexCode indices (.inl (ivar i)), indexCode indices (.inr (factor i))]

def incidenceSelectedPlan (indices : List (V ⊕ E)) (currentSize : ℕ)
    (remaining : List ℕ) (i : I) : List ℕ :=
  ReadPlan.completionPlan currentSize remaining (incidenceReadPlan ivar factor indices i)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceReadPlan_valid (indices : List (V ⊕ E))
    (hi : ∀ a, a ∈ indices) (i : I) (n : ℕ)
    (hn : n ∈ incidenceReadPlan ivar factor indices i) : n < indices.length := by
  let _ : BEq (V ⊕ E) := instBEqOfDecidableEq
  simp only [incidenceReadPlan, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl <;> exact List.idxOf_lt_length_iff.mpr (hi _)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
theorem encode_incidenceType (ω : WordAssignment V E r Q) (i : I) :
    CollisionProgram.encodeType (incidenceType ivar factor ω i) =
      ReadPlan.encodeWord (ω (.inl (ivar i))) ++
      ReadPlan.encodeWord (ω (.inr (factor i))) := by
  rw [ReadPlan.encodeType_eq_words]
  simp [List.ofFn_succ, CollisionProgram.registerWord, incidenceType]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem gather_incidenceSelectedPlan (indices : List (V ⊕ E))
    (hi : ∀ a, a ∈ indices) (default : Word r Q) (current candidate : List (Word r Q))
    (remaining : List ℕ) (hc : indices.length ≤ current.length)
    (hr : remaining.length ≤ candidate.length) (i : I) :
    GatherProgram.gathered ((current ++ candidate).map ReadPlan.encodeWord)
      (incidenceSelectedPlan ivar factor indices current.length remaining i) =
      CollisionProgram.encodeType (incidenceType ivar factor
        (fun a => ReadPlan.completedAt default current remaining candidate (indexCode indices a)) i) := by
  let _ : BEq (V ⊕ E) := instBEqOfDecidableEq
  have hget (n : ℕ) (hn : n < current.length) :
      ((current ++ candidate).map ReadPlan.encodeWord).getD
        (ReadPlan.selectPosition current.length remaining n) [] =
        ReadPlan.encodeWord (ReadPlan.completedAt default current remaining candidate n) := by
    rw [ReadPlan.getD_map_of_lt ReadPlan.encodeWord _ default [] _
      (by simpa using ReadPlan.selected_valid current.length candidate.length remaining hr n hn),
      ReadPlan.selected_getD default current remaining candidate n hn]
  rw [encode_incidenceType]
  simp only [GatherProgram.gathered, incidenceSelectedPlan, ReadPlan.completionPlan,
    incidenceReadPlan, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [hget (indexCode indices (.inl (ivar i))) ((List.idxOf_lt_length_iff.mpr (hi _)).trans_le hc),
    hget (indexCode indices (.inr (factor i))) ((List.idxOf_lt_length_iff.mpr (hi _)).trans_le hc)]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidence_leafBit_eq (indices : List (V ⊕ E))
    (hi : ∀ a, a ∈ indices) (default : Word r Q) (current candidate : List (Word r Q))
    (remaining : List ℕ) (hc : indices.length ≤ current.length)
    (hr : remaining.length ≤ candidate.length) (i j : I) :
    CollisionTupleProgram.leafBit (CollisionTupleProgram.tupleBytes current)
      (ReadPlan.wordWidth r Q)
      (incidenceSelectedPlan ivar factor indices current.length remaining i)
      (incidenceSelectedPlan ivar factor indices current.length remaining j)
      (CollisionTupleProgram.tupleBytes candidate) =
      numberedIncidenceTest ivar factor indices (.inl (i,j))
        (ReadPlan.completedAt default current remaining candidate) := by
  have hrows : ∀ row ∈ current.map ReadPlan.encodeWord ++ candidate.map ReadPlan.encodeWord,
      row.length = ReadPlan.wordWidth r Q := by
    intro row hrow
    rcases List.mem_append.mp hrow with hrow | hrow <;>
      obtain ⟨word, _, rfl⟩ := List.mem_map.mp hrow <;> exact ReadPlan.encodeWord_length _
  rw [CollisionTupleProgram.tupleBytes, CollisionTupleProgram.tupleBytes,
    CollisionTupleProgram.leafBit_eq_collision _ _ _ hrows, ← List.map_append]
  unfold CollisionStreamProgram.collisionBit
  rw [gather_incidenceSelectedPlan ivar factor indices hi default current candidate remaining hc hr i,
      gather_incidenceSelectedPlan ivar factor indices hi default current candidate remaining hc hr j]
  simp only [CollisionProgram.encodeType_eq_iff, numberedIncidenceTest, incidenceWords_eq_iff]

def generatedIncidenceLeaves (alphabet : List (Word r Q)) (indices : List (V ⊕ E))
    (current : List (Word r Q)) (remaining : List ℕ) (i j : I) : List Bool :=
  CollisionTupleProgram.streamed (CollisionTupleProgram.tupleBytes current)
    (ReadPlan.wordWidth r Q)
    (incidenceSelectedPlan ivar factor indices current.length remaining i)
    (incidenceSelectedPlan ivar factor indices current.length remaining j)
    (TupleProgram.powerRows (alphabet.map ReadPlan.encodeWord) 4 [[]]) []

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem generatedIncidenceLeaves_perm (alphabet : List (Word r Q))
    (indices : List (V ⊕ E)) (hi : ∀ a, a ∈ indices) (default : Word r Q)
    (current : List (Word r Q)) (remaining : List ℕ)
    (hc : indices.length ≤ current.length) (hr : remaining.length ≤ 4) (i j : I) :
    (generatedIncidenceLeaves ivar factor alphabet indices current remaining i j).Perm
      ((CoefficientSearch.tuples alphabet 4).map fun candidate =>
        numberedIncidenceTest ivar factor indices (.inl (i,j))
          (ReadPlan.completedAt default current remaining (List.ofFn candidate))) := by
  let test := CollisionTupleProgram.leafBit (CollisionTupleProgram.tupleBytes current)
    (ReadPlan.wordWidth r Q)
    (incidenceSelectedPlan ivar factor indices current.length remaining i)
    (incidenceSelectedPlan ivar factor indices current.length remaining j)
  have h := (CollisionGenerateRefinement.generated_word_perm alphabet 4).map test
  have heq : ((CoefficientSearch.tuples alphabet 4).map
      (fun candidate => CollisionTupleProgram.tupleBytes (List.ofFn candidate))).map test =
      (CoefficientSearch.tuples alphabet 4).map (fun candidate =>
        numberedIncidenceTest ivar factor indices (.inl (i,j))
          (ReadPlan.completedAt default current remaining (List.ofFn candidate))) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro candidate _
    exact incidence_leafBit_eq ivar factor indices hi default current _ remaining hc
      (by simpa using hr) i j
  rw [heq] at h
  have hrev := List.reverse_perm
    ((TupleProgram.powerRows (alphabet.map ReadPlan.encodeWord) 4 [[]]).map test)
  simpa only [generatedIncidenceLeaves, CollisionTupleProgram.streamed_eq_reverse_map,
    List.append_nil] using hrev.trans h

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem numberedIncidenceTest_currentArray (indices : List (V ⊕ E))
    (hi : ∀ a, a ∈ indices) (default : Word r Q) (fixed candidate : List (Word r Q))
    (remaining : List ℕ) (hn : remaining.Nodup) (hr : remaining.length ≤ candidate.length)
    (z : ScoreTerm I V Q) :
    numberedIncidenceTest ivar factor indices z
      (ReadPlan.completedAt default (ReadPlan.currentArray default indices.length fixed)
        remaining candidate) =
    numberedIncidenceTest ivar factor indices z
      (ReadPlan.applyChoices (decode default fixed)
        (PaddedCompletion.paddedIndices remaining 4) candidate) := by
  let _ : BEq (V ⊕ E) := instBEqOfDecidableEq
  have heq : (fun a : V ⊕ E => ReadPlan.completedAt default
        (ReadPlan.currentArray default indices.length fixed) remaining candidate
        (indexCode indices a)) =
      (fun a => ReadPlan.applyChoices (decode default fixed)
        (PaddedCompletion.paddedIndices remaining 4) candidate (indexCode indices a)) := by
    funext a
    unfold PaddedCompletion.paddedIndices
    rw [ReadPlan.applyChoices_padding, ReadPlan.applyChoices_real default _ _ _ hn hr]
    unfold ReadPlan.completedAt
    split_ifs
    · rfl
    · exact ReadPlan.currentArray_getD default indices.length fixed _
        (List.idxOf_lt_length_iff.mpr (hi _))
  cases z with
  | inl p => simp only [numberedIncidenceTest, heq]
  | inr p => rfl

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem generatedIncidencePair_perm (alphabet : List (Word r Q))
    (indices : List (V ⊕ E)) (hi : ∀ a, a ∈ indices) (default : Word r Q)
    (fixed : List (Word r Q)) (remaining : List ℕ) (hn : remaining.Nodup) (i j : I) :
    (generatedIncidenceLeaves ivar factor alphabet indices
      (ReadPlan.currentArray default indices.length fixed)
      (active (numberedScoreSupport (Q := Q) ivar factor indices (.inl (i,j))) remaining) i j).Perm
      (incidenceCompletionLeaves ivar factor alphabet indices (.inl (i,j)) remaining
        (decode default fixed)) := by
  let support := numberedScoreSupport (Q := Q) ivar factor indices (.inl (i,j))
  have hlen : (active support remaining).length ≤ 4 :=
    numberedActive_length_le ivar factor indices (.inl (i,j)) remaining hn
  have h := generatedIncidenceLeaves_perm ivar factor alphabet indices hi default
    (ReadPlan.currentArray default indices.length fixed) (active support remaining)
    (by simp) hlen i j
  have heq : ((CoefficientSearch.tuples alphabet 4).map fun candidate =>
      numberedIncidenceTest ivar factor indices (.inl (i,j))
        (ReadPlan.completedAt default (ReadPlan.currentArray default indices.length fixed)
          (active support remaining) (List.ofFn candidate))) =
      incidenceCompletionLeaves ivar factor alphabet indices (.inl (i,j)) remaining
        (decode default fixed) := by
    unfold incidenceCompletionLeaves PaddedCompletion.paddedLeaves
    rw [ReadPlan.leaves_eq_tuples, PaddedCompletion.paddedIndices_length _ _ hlen]
    apply congrArg (fun f => (CoefficientSearch.tuples alphabet 4).map f)
    funext candidate
    exact numberedIncidenceTest_currentArray ivar factor indices hi default fixed _ _
      (hn.filter _) (by simpa [active] using hlen) _
  rw [heq] at h
  exact h

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem generatedIncidencePair_count (alphabet : List (Word r Q))
    (indices : List (V ⊕ E)) (hi : ∀ a, a ∈ indices) (default : Word r Q)
    (fixed : List (Word r Q)) (remaining : List ℕ) (hn : remaining.Nodup) (i j : I) :
    PaddedCompletion.trueCount (generatedIncidenceLeaves ivar factor alphabet indices
      (ReadPlan.currentArray default indices.length fixed)
      (active (numberedScoreSupport (Q := Q) ivar factor indices (.inl (i,j))) remaining) i j) =
      scaledCount alphabet (fun η => PackingProgram.incidenceIndicator ivar factor
        (.inl (i,j)) (fun a => η (indexCode indices a)))
        (numberedScoreSupport (Q := Q) ivar factor indices (.inl (i,j))) 4 remaining
        (decode default fixed) := by
  rw [← incidenceCompletionLeaves_count]
  exact ((generatedIncidencePair_perm ivar factor alphabet indices hi default fixed
    remaining hn i j).filter id).length_eq

end Plans
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
