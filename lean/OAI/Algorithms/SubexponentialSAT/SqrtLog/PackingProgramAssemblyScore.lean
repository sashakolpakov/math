import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyPrefix
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramReducedWeights
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgramSize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidatesBounds

namespace OAI.Algorithms

/-! Exact values and uniform bounds for the two physically produced streams. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp

section Scores
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

def candidateScore (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (default : Word r Q) (heads s M n : ℕ)
    (fixed : List (Word r Q)) (candidate : Word r Q) : ℕ :=
  reducedScore heads s M r
    (PackingIncidenceProgram.incidenceNumerator ivar factor alphabet pairs indices default n (candidate::fixed))
    (overlap heads fixed candidate)

def evaluate (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (default : Word r Q) (heads s M n : ℕ)
    (fixed : List (Word r Q)) : ℕ :=
  match fixed with
  | [] => 0
  | candidate::prior => candidateScore ivar factor alphabet pairs indices default heads s M n prior candidate

def scorePairs (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (default : Word r Q) (heads n : ℕ)
    (fixed : List (Word r Q)) : List (ℕ × ℕ) :=
  alphabet.map (fun candidate =>
    (PackingIncidenceProgram.incidenceNumerator ivar factor alphabet pairs indices default n (candidate::fixed),
     overlap heads fixed candidate))

theorem overlap_le (heads : ℕ) (fixed : List (Word r Q)) (candidate : Word r Q) :
    overlap heads fixed candidate ≤ fixed.length*ReadPlan.wordWidth r Q := by
  have h := PackingHeadProgramCandidates.score_le (ReadPlan.encodeWord candidate) (headRows heads fixed)
  rw [ReadPlan.encodeWord_length,headRows_length] at h
  exact h.trans (Nat.mul_le_mul_right _ (headCount_le heads fixed))

def scoreBound (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (heads s M : ℕ) : ℕ :=
  (heads*s)^2*(pairs.length*alphabet.length^4)+8*(M*r)^2*(indices.length*ReadPlan.wordWidth r Q)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem candidateScore_bound (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (default : Word r Q) (heads s M n : ℕ)
    (fixed : List (Word r Q)) (candidate : Word r Q) (hsize : fixed.length ≤ indices.length) :
    candidateScore ivar factor alphabet pairs indices default heads s M n fixed candidate ≤
      scoreBound alphabet pairs indices heads s M := by
  apply reducedScore_bound
  · exact PackingIncidenceProgram.incidenceNumerator_le ivar factor alphabet pairs indices default n _
  · exact (overlap_le heads fixed candidate).trans (Nat.mul_le_mul_right _ hsize)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem evaluate_bound (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (default : Word r Q) (heads s M n : ℕ)
    (fixed : List (Word r Q)) (candidate : Word r Q) (hsize : n+1+fixed.length ≤ indices.length) :
    evaluate ivar factor alphabet pairs indices default heads s M n (candidate::fixed) ≤
      scoreBound alphabet pairs indices heads s M :=
  candidateScore_bound ivar factor alphabet pairs indices default heads s M n fixed candidate (by omega)

end Scores
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
