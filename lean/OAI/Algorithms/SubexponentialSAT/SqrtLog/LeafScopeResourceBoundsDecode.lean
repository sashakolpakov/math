import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramCandidate
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamilyPayloadSelect

namespace OAI.Algorithms

/-! A single raw-slot decoder for the actual logical records returned by the
selector's parser. It retains zero-coefficient and repeated entries. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open HashSelectProgram

def listCandidate {m : ℕ} (row : List (Fin m × ZMod 3)) : HashFamily.Candidate m row.length :=
  (fun j => (row.get j).1, fun j => (row.get j).2)

theorem listCandidate_terms {m : ℕ} (row : List (Fin m × ZMod 3)) :
    HashInputProgram.candidateTerms (listCandidate row) = row := by
  simp [HashInputProgram.candidateTerms, listCandidate]

abbrev rawDecode (m width : ℕ) (hm : 0 < m) (payload : List Bool) :=
  HashInputProgram.candidateTerms (HashFamilyPayload.decode m (payload.length / width) width hm payload)

theorem rawDecode_length (m width : ℕ) (hm : 0 < m) (payload : List Bool) :
    (rawDecode m width hm payload).length = payload.length / width := by
  simp [rawDecode, HashInputProgram.candidateTerms]

theorem listCandidate_encode {m : ℕ} (width : ℕ) (row : List (Fin m × ZMod 3)) :
    HashFamilyPayload.encode width (listCandidate row) = (CodeRowsProgram.rowPayload width m row).reverse := by
  rw [← HashInputProgram.candidate_rawInput, listCandidate_terms]
  rfl

theorem rawDecode_rowPayload {m width : ℕ} (hm : 0 < m) (hw : 3*m ≤ 2^width)
    (row : List (Fin m × ZMod 3)) :
    rawDecode m width hm (CodeRowsProgram.rowPayload width m row).reverse = row := by
  have hlen : (CodeRowsProgram.rowPayload width m row).reverse.length / width = row.length := by
    rw [List.length_reverse, CodeRowsProgram.rowPayload_length,
      Nat.mul_div_cancel _ (HashFamilyPayload.width_pos hm hw)]
  unfold rawDecode
  rw [hlen, ← listCandidate_encode, HashFamilyPayload.decode_encode hm width hw,
    listCandidate_terms]

theorem rawDecode_generated_length {m width depth : ℕ} (hm : 0 < m) (hw : 3*m ≤ 2^width)
    (payload : List Bool) (hp : payload ∈ generatedPayloads (HashFamilyPayload.alphabet m width) depth) :
    (rawDecode m width hm payload).length = depth := by
  rw [rawDecode_length, HashFamilyPayload.generated_payload_width m width depth payload hp,
    Nat.mul_div_cancel _ (HashFamilyPayload.width_pos hm hw)]

/-- Exact physical payload recovery for every generated candidate. -/
theorem rawDecode_generated_payload {m width depth : ℕ} (hm : 0 < m) (hw : 3*m ≤ 2^width)
    (payload : List Bool) (hp : payload ∈ generatedPayloads (HashFamilyPayload.alphabet m width) depth) :
    (CodeRowsProgram.rowPayload width m (rawDecode m width hm payload)).reverse = payload := by
  have hlen : payload.length / width = depth := by
    rw [HashFamilyPayload.generated_payload_width m width depth payload hp,
      Nat.mul_div_cancel _ (HashFamilyPayload.width_pos hm hw)]
  change HashInputProgram.Loop.rawInput width (rawDecode m width hm payload) = payload
  unfold rawDecode
  rw [hlen, HashInputProgram.candidate_rawInput]
  exact HashFamilyPayload.encode_decode_generated hm hw payload hp

abbrev initialPayloads {m : ℕ} (width : ℕ) (rows : List (List (Fin m × ZMod 3))) :=
  rows.map fun row => (CodeRowsProgram.rowPayload width m row).reverse

theorem initialPayloads_decode {m width : ℕ} (hm : 0 < m) (hw : 3*m ≤ 2^width)
    (rows : List (List (Fin m × ZMod 3))) :
    (initialPayloads width rows).map (rawDecode m width hm) = rows := by
  simp [initialPayloads, List.map_map, Function.comp_def, rawDecode_rowPayload hm hw]

/-- This is an equality of existing bit streams, not an uncharged reversal.
`candidateEncoding` already frames the reverse of every logical record. -/
theorem initialPayloads_encoding {m : ℕ} (width : ℕ) (rows : List (List (Fin m × ZMod 3))) :
    candidateEncoding (initialPayloads width rows) =
      Encoding.encodeList (CodeRowsProgram.rowPayload width m) rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [initialPayloads, candidateEncoding, Encoding.encodeList, ih]

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
