import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Encoding

namespace OAI.Algorithms

/-!
# Shared record representation for executable programs

A scalar is stored as a Boolean payload (little-endian bits for natural
numbers; the scalar module specifies any fixed padding). A record list uses
the existing `Encoding.encodeList id`: false terminates the list; true starts
an escaped frame. Matrices and other fixed-depth schemas nest this same
representation. These are executable decoders and exact size identities,
not assertions that a machine has run them.
-/

namespace SubexponentialSAT.ProgramEncoding

abbrev Records := List (List Bool)

abbrev encodeRecords (records : Records) : List Bool :=
  Encoding.encodeList id records

/-- Explicitly bounded recursive decoder. Every record consumes a leading
tag, so input length plus one is sufficient fuel. -/
def readRecordsAux : ℕ → List Bool → Option (Records × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: rest => do
      let (payload, afterPayload) ← Encoding.readFrame rest
      let (records, tail) ← readRecordsAux fuel afterPayload
      pure (payload :: records, tail)

def readRecords (input : List Bool) : Option (Records × List Bool) :=
  readRecordsAux (input.length + 1) input

theorem readRecordsAux_encodeList_append (records : Records) (rest : List Bool)
    (fuel : ℕ) (hfuel : records.length < fuel) :
    readRecordsAux fuel (encodeRecords records ++ rest) = some (records, rest) := by
  induction records generalizing fuel with
  | nil =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel => rfl
  | cons payload records ih =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have htail : records.length < fuel := by simp only [List.length_cons] at hfuel; omega
          simp only [encodeRecords, Encoding.encodeList, List.cons_append,
            List.append_assoc, readRecordsAux, Encoding.readFrame_frame_append, id_eq]
          change (readRecordsAux fuel (encodeRecords records ++ rest)).bind
            (fun result => some (payload :: result.1, result.2)) =
              some (payload :: records, rest)
          rw [ih fuel htail]
          rfl

theorem encodeRecords_length (records : Records) :
    (encodeRecords records).length =
      2 * (records.map List.length).sum + 2 * records.length + 1 := by
  induction records with
  | nil => rfl
  | cons payload records ih =>
      change (Encoding.encodeList id (payload :: records)).length = _
      rw [Encoding.length_encodeList_cons]
      change 2 * payload.length + 2 + (encodeRecords records).length = _
      rw [ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem readRecords_encodeList_append (records : Records) (rest : List Bool) :
    readRecords (encodeRecords records ++ rest) = some (records, rest) := by
  apply readRecordsAux_encodeList_append
  rw [List.length_append, encodeRecords_length]
  omega

@[simp] theorem readRecords_encodeRecords (records : Records) :
    readRecords (encodeRecords records) = some (records, []) := by
  simpa using readRecords_encodeList_append records []

private theorem frame_input_shape : (input payload rest : List Bool) →
    Encoding.readFrame input = some (payload, rest) →
      input = Encoding.frame payload ++ rest
  | [], payload, rest, h => by simp [Encoding.readFrame] at h
  | false :: input, payload, rest, h => by
      have hp : ([], input) = (payload, rest) := Option.some.inj (by
        simpa [Encoding.readFrame] using h)
      obtain ⟨hb, hr⟩ := Prod.mk.inj hp
      subst payload
      subst rest
      rfl
  | true :: [], payload, rest, h => by simp [Encoding.readFrame] at h
  | true :: bit :: input, payload, rest, h => by
      cases hr : Encoding.readFrame input with
      | none => simp [Encoding.readFrame, hr] at h
      | some result =>
          rcases result with ⟨more, tail⟩
          have hp : (bit :: more, tail) = (payload, rest) := Option.some.inj (by
            simpa [Encoding.readFrame, hr] using h)
          obtain ⟨hb, ht⟩ := Prod.mk.inj hp
          subst payload
          subst rest
          have hi := frame_input_shape input more tail hr
          simpa [Encoding.frame] using congrArg (fun xs => true :: bit :: xs) hi

/-- Successful decoding determines exactly the consumed prefix. -/
theorem readRecordsAux_sound {fuel : ℕ} {input rest : List Bool} {records : Records}
    (h : readRecordsAux fuel input = some (records, rest)) :
    input = encodeRecords records ++ rest := by
  induction fuel generalizing input rest records with
  | zero => simp [readRecordsAux] at h
  | succ fuel ih =>
      cases input with
      | nil => simp [readRecordsAux] at h
      | cons tag input =>
          cases tag with
          | false =>
              have hp : ([], input) = (records, rest) := Option.some.inj h
              obtain ⟨hr, ht⟩ := Prod.mk.inj hp
              subst records
              subst rest
              rfl
          | true =>
              cases hp : Encoding.readFrame input with
              | none => simp [readRecordsAux, hp] at h
              | some result =>
                  rcases result with ⟨payload, afterPayload⟩
                  cases hm : readRecordsAux fuel afterPayload with
                  | none => simp [readRecordsAux, hp, hm] at h
                  | some result =>
                      rcases result with ⟨more, tail⟩
                      have hr' : (payload :: more, tail) = (records, rest) :=
                        Option.some.inj (by simpa [readRecordsAux, hp, hm] using h)
                      obtain ⟨heq, hrest⟩ := Prod.mk.inj hr'
                      subst records
                      subst rest
                      have hframe := frame_input_shape input payload afterPayload hp
                      have htail := ih hm
                      simp [hframe, htail, encodeRecords, Encoding.encodeList, List.append_assoc]

theorem readRecords_sound {input rest : List Bool} {records : Records}
    (h : readRecords input = some (records, rest)) :
    input = encodeRecords records ++ rest :=
  readRecordsAux_sound h

theorem readRecords_consumed_length {input rest : List Bool} {records : Records}
    (h : readRecords input = some (records, rest)) :
    input.length = 2 * (records.map List.length).sum + 2 * records.length + 1 + rest.length := by
  rw [readRecords_sound h, List.length_append, encodeRecords_length]

def encodeMatrix (rows : List Records) : List Bool :=
  encodeRecords (rows.map encodeRecords)

theorem encodeMatrix_length (rows : List Records) :
    (encodeMatrix rows).length =
      4 * (rows.map fun row => (row.map List.length).sum).sum +
      4 * (rows.map List.length).sum + 4 * rows.length + 1 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      change (Encoding.encodeList id (encodeRecords row :: rows.map encodeRecords)).length = _
      rw [Encoding.length_encodeList_cons]
      change 2 * (encodeRecords row).length + 2 + (encodeMatrix rows).length = _
      rw [encodeRecords_length, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem encodeRecords_length_le (records : Records) (width : ℕ)
    (hwidth : ∀ payload ∈ records, payload.length ≤ width) :
    (encodeRecords records).length ≤ 1 + (2 * width + 2) * records.length :=
  Encoding.length_encodeList_upper id records width hwidth

end SubexponentialSAT.ProgramEncoding

end OAI.Algorithms
