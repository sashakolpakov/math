import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGeneratedWords
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramBounds

namespace OAI.Algorithms

/-! Exact sizes of the physical generated record lists. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

def wordRecordsLength (D : ℕ) := (10 * D + 2) * 3 ^ D + 1

theorem encoded_words_length {D : ℕ} (values : List (Fin D → SparseCode.F3)) :
    (Encoding.encodeList (fun x => scalarFrames (List.ofFn x)) values).length =
      (10 * D + 2) * values.length + 1 := by
  induction values with
  | nil => simp [Encoding.encodeList]
  | cons x xs ih =>
      rw [Encoding.length_encodeList_cons, ih, scalarFrames_ternary_length,
        List.length_ofFn, List.length_cons]
      ring

theorem generated_words_length (D : ℕ) :
    (ProgramEncoding.encodeRecords (framedCandidates 3 D)).length = wordRecordsLength D := by
  obtain ⟨values,hvalues,hlen,_⟩ := generated_words_typed D
  have h := encoded_words_length values
  rw [encodeList_map_records, hvalues, hlen] at h
  exact h

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
