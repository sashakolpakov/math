import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramBinaryGenerated
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGraphBounds

namespace OAI.Algorithms

/-! Exact sizes of the physical generated record lists. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

def characterRecordsLength (D : ℕ) := (10 * D + 2) * 2 ^ D + 1

theorem encoded_characters_length {D : ℕ} (values : List (Fin D → ZMod 2)) :
    (Encoding.encodeList (fun x => scalarFrames (List.ofFn x)) values).length =
      (10 * D + 2) * values.length + 1 := by
  induction values with
  | nil => simp [Encoding.encodeList]
  | cons x xs ih =>
      rw [Encoding.length_encodeList_cons, ih, scalarFrames_binary_length,
        List.length_ofFn, List.length_cons]
      ring

theorem generated_characters_length (D : ℕ) :
    (ProgramEncoding.encodeRecords (framedCandidates 2 D)).length = characterRecordsLength D := by
  obtain ⟨values,hvalues,hlen,_⟩ := generated_characters_typed D
  have h := encoded_characters_length values
  rw [encodeList_map_records, hvalues, hlen] at h
  exact h

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
