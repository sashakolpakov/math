import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramRepresentation

namespace OAI.Algorithms

/-! A proof-only typed view of the words produced by the fixed tuple machine.
The order need not agree with any other finite enumeration. No decoding or
choice operation is executed by the bit program. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

private theorem list_lift {α β : Type*} (f : α → β) (ys : List β)
    (h : ∀ y ∈ ys, ∃ x, f x = y) : ∃ xs : List α, xs.map f = ys := by
  induction ys with
  | nil => exact ⟨[],rfl⟩
  | cons y ys ih =>
      obtain ⟨x,hx⟩ := h y (by simp)
      obtain ⟨xs,hxs⟩ := ih (fun z hz => h z (by simp [hz]))
      exact ⟨x :: xs, by simp [hx,hxs]⟩

theorem generated_words_typed (D : ℕ) :
    ∃ values : List (Fin D → SparseCode.F3),
      values.map (fun x => scalarFrames (List.ofFn x)) = framedCandidates 3 D ∧
      values.length = 3 ^ D ∧ (∀ x, x ∈ values) := by
  obtain ⟨values,hvalues⟩ := list_lift (fun x : Fin D → SparseCode.F3 =>
    scalarFrames (List.ofFn x)) (framedCandidates 3 D) (by
      intro bits hb
      obtain ⟨v,hv⟩ := (framedCandidates_sound bits).mp hb
      exact ⟨v, by simpa only [framedVector_eq_scalarFrames] using hv⟩)
  refine ⟨values,hvalues,?_,?_⟩
  · have h := congrArg List.length hvalues
    simpa using h
  · intro x
    have hx : scalarFrames (List.ofFn x) ∈
        values.map (fun x => scalarFrames (List.ofFn x)) := by
      rw [hvalues, ← framedVector_eq_scalarFrames]
      exact framedCandidates_complete x
    obtain ⟨v,hv,hvx⟩ := List.mem_map.mp hx
    have heq : v = x := by
      apply SubexpTupleRefinement.encodeTuple_injective (framedScalarCode 3)
      change framedVector v = framedVector x
      simpa only [← framedVector_eq_scalarFrames] using hvx
    simpa [heq] using hv

theorem encodeList_map_records {α : Type*} (enc : α → List Bool) (values : List α) :
    Encoding.encodeList enc values = ProgramEncoding.encodeRecords (values.map enc) := by
  induction values with
  | nil => rfl
  | cons x xs ih =>
      simpa [ProgramEncoding.encodeRecords, Encoding.encodeList] using
        congrArg (fun rest => true :: (Encoding.frame (enc x) ++ rest)) ih


theorem generated_matrices_typed (t D : ℕ) :
    ∃ values : List (Fin t → Fin D → SparseCode.F3),
      values.map matrixFrames = framedCandidates 3 (t * D) ∧
      values.length = 3 ^ (t * D) ∧ (∀ Q, Q ∈ values) := by
  obtain ⟨words,hw,hlen,hcomplete⟩ := generated_words_typed (t * D)
  refine ⟨words.map (expandMatrix (rows := t) (cols := D)), ?_, ?_, ?_⟩
  · rw [List.map_map]
    have heq : (fun Q : Fin t → Fin D → SparseCode.F3 => matrixFrames Q) ∘
        (expandMatrix (p := 3) (rows := t) (cols := D)) =
        (fun x : Fin (t * D) → SparseCode.F3 => scalarFrames (List.ofFn x)) := by
      funext x
      change matrixFrames (expandMatrix (rows := t) (cols := D) x) = scalarFrames (List.ofFn x)
      rw [← framedMatrix_eq_matrixFrames]
      simp only [ framedMatrix, flatten_expand,
        framedVector_eq_scalarFrames]
    rw [heq,hw]
  · simpa using hlen
  · intro Q
    exact List.mem_map.mpr ⟨flattenMatrix Q,hcomplete _,expand_flatten Q⟩

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
