import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingRelations
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramCounts

namespace OAI.Algorithms

/-! Boolean local completion trees for the two exact packing score counters. -/
namespace SubexponentialSAT.SqrtLog.Packing
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.Subexp.PaddedCompletion SubexponentialSAT.Subexp.ReadPlan

section Completion
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

/-- A collision is equality of the two actual word records, with shared seeds read once. -/
def numberedIncidenceTest (indices : List (V ⊕ E)) :
    ScoreTerm I V Q → (ℕ → Word r Q) → Bool
  | .inl (i,j), η => decide
      (incidenceWords ivar factor (fun a => η (indexCode indices a)) i =
       incidenceWords ivar factor (fun a => η (indexCode indices a)) j)
  | .inr _, _ => false

def numberedHeadTest (indices : List (V ⊕ E)) :
    ScoreTerm I V Q → (ℕ → Word r Q) → Bool
  | .inl _, _ => false
  | .inr (t,v,u), η => decide
      (η (indexCode indices (.inl v)) t = η (indexCode indices (.inl u)) t)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem numberedIncidenceTest_value (indices : List (V ⊕ E))
    (z : ScoreTerm I V Q) (η : ℕ → Word r Q) :
    boolValue (numberedIncidenceTest ivar factor indices z η) =
      PackingProgram.incidenceIndicator ivar factor z (fun a => η (indexCode indices a)) := by
  cases z with
  | inl p => rcases p with ⟨i,j⟩; simp [numberedIncidenceTest, incidenceWords_eq_iff,
      boolValue, PackingProgram.incidenceIndicator]
  | inr p => rfl

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem numberedHeadTest_value (indices : List (V ⊕ E))
    (z : ScoreTerm I V Q) (η : ℕ → Word r Q) :
    boolValue (numberedHeadTest indices z η) =
      PackingProgram.headIndicator z (fun a => η (indexCode indices a)) := by
  cases z with
  | inl p => rfl
  | inr p => rcases p with ⟨t,v,u⟩; simp [numberedHeadTest, boolValue,
      PackingProgram.headIndicator]

def incidenceCompletionLeaves (alphabet : List (Word r Q)) (indices : List (V ⊕ E))
    (z : ScoreTerm I V Q) (remaining : List ℕ) (η : ℕ → Word r Q) : List Bool :=
  paddedLeaves alphabet (numberedIncidenceTest ivar factor indices z)
    (active (numberedScoreSupport ivar factor indices z) remaining) 4 η

def headCompletionLeaves (alphabet : List (Word r Q)) (indices : List (V ⊕ E))
    (z : ScoreTerm I V Q) (remaining : List ℕ) (η : ℕ → Word r Q) : List Bool :=
  paddedLeaves alphabet (numberedHeadTest indices z)
    (active (numberedScoreSupport ivar factor indices z) remaining) 4 η

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceCompletionLeaves_count (alphabet : List (Word r Q))
    (indices : List (V ⊕ E)) (z : ScoreTerm I V Q) (remaining : List ℕ)
    (η : ℕ → Word r Q) :
    trueCount (incidenceCompletionLeaves ivar factor alphabet indices z remaining η) =
      scaledCount alphabet
        (fun ξ => PackingProgram.incidenceIndicator ivar factor z
          (fun a => ξ (indexCode indices a)))
        (numberedScoreSupport ivar factor indices z) 4 remaining η := by
  unfold incidenceCompletionLeaves
  rw [trueCount_paddedLeaves]
  simp only [numberedIncidenceTest_value]
  rfl

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem headCompletionLeaves_count (alphabet : List (Word r Q))
    (indices : List (V ⊕ E)) (z : ScoreTerm I V Q) (remaining : List ℕ)
    (η : ℕ → Word r Q) :
    trueCount (headCompletionLeaves ivar factor alphabet indices z remaining η) =
      scaledCount alphabet
        (fun ξ => PackingProgram.headIndicator z (fun a => ξ (indexCode indices a)))
        (numberedScoreSupport ivar factor indices z) 4 remaining η := by
  unfold headCompletionLeaves
  rw [trueCount_paddedLeaves]
  simp only [numberedHeadTest_value]
  rfl

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceCompletionLeaves_count_sum (alphabet : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E))
    (remaining : List ℕ) (η : ℕ → Word r Q) :
    trueCount (terms.flatMap (fun z =>
      incidenceCompletionLeaves ivar factor alphabet indices z remaining η)) =
        (PackingProgram.unweightedCounts ivar factor alphabet terms indices remaining η).1 := by
  rw [trueCount_flatMap]
  simp only [incidenceCompletionLeaves_count]
  rfl

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem headCompletionLeaves_count_sum (alphabet : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E))
    (remaining : List ℕ) (η : ℕ → Word r Q) :
    trueCount (terms.flatMap (fun z =>
      headCompletionLeaves ivar factor alphabet indices z remaining η)) =
        (PackingProgram.unweightedCounts ivar factor alphabet terms indices remaining η).2 := by
  rw [trueCount_flatMap]
  simp only [headCompletionLeaves_count]
  rfl

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem numberedActive_length_le (indices : List (V ⊕ E)) (z : ScoreTerm I V Q)
    (remaining : List ℕ) (hn : remaining.Nodup) :
    (active (numberedScoreSupport ivar factor indices z) remaining).length ≤ 4 :=
  (active_length_le _ _ hn).trans (numberedScoreSupport_card_le ivar factor indices z)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceCompletionLeaves_eq_tuples (alphabet : List (Word r Q))
    (indices : List (V ⊕ E)) (z : ScoreTerm I V Q) (remaining : List ℕ)
    (hn : remaining.Nodup) (default : Word r Q) (current : List (Word r Q)) :
    incidenceCompletionLeaves ivar factor alphabet indices z remaining
      (fun n => current.getD n default) =
      (SubexponentialSAT.Subexp.CoefficientSearch.tuples alphabet 4).map (fun candidate =>
        numberedIncidenceTest ivar factor indices z
          (completedAt default current
            (active (numberedScoreSupport ivar factor indices z) remaining)
            (List.ofFn candidate))) := by
  unfold incidenceCompletionLeaves paddedLeaves
  rw [leaves_eq_tuples, paddedIndices_length _ _
    (numberedActive_length_le ivar factor indices z remaining hn)]
  apply congrArg (fun f => (SubexponentialSAT.Subexp.CoefficientSearch.tuples alphabet 4).map f)
  funext candidate
  have heq : applyChoices (fun n => current.getD n default)
      (paddedIndices (active (numberedScoreSupport ivar factor indices z) remaining) 4)
      (List.ofFn candidate) =
        completedAt default current
          (active (numberedScoreSupport ivar factor indices z) remaining)
          (List.ofFn candidate) := by
    funext n
    apply applyChoices_padded
    · exact hn.filter _
    · simpa using numberedActive_length_le ivar factor indices z remaining hn
  rw [heq]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
/-- The concrete two-record predicate after a padded local tuple has been selected. -/
theorem numberedIncidenceTest_completed (indices : List (V ⊕ E)) (i j : I)
    (default : Word r Q) (current candidate : List (Word r Q)) (activeIndices : List ℕ) :
    numberedIncidenceTest ivar factor indices (.inl (i,j))
      (completedAt default current activeIndices candidate) =
      decide ([completedAt default current activeIndices candidate
          (indexCode indices (.inl (ivar i))),
        completedAt default current activeIndices candidate
          (indexCode indices (.inr (factor i)))] =
       [completedAt default current activeIndices candidate
          (indexCode indices (.inl (ivar j))),
        completedAt default current activeIndices candidate
          (indexCode indices (.inr (factor j)))]) := rfl

end Completion
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
