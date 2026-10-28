import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketTable

namespace OAI.Algorithms

/-! Polynomial serialized-input bounds for the actual all-type bucket program. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open MatrixProgramSupport

theorem table_payload_bound (records : List BucketProgram.Record) (keys : List (List Bool))
    (T : ℕ) (hkeys : ∀ key ∈ keys, key.length ≤ T) :
    ∀ payload ∈ table records keys,
      payload.length ≤ 2 * T + 1 + (BucketProgram.encodeRecords records).length := by
  intro payload hp
  obtain ⟨key, hk, rfl⟩ := List.mem_map.mp hp
  have hq := hkeys key hk
  have hb := selected_words_length_le records key
  simp only [bucketPayload, List.length_append, Encoding.length_frame]
  omega

theorem table_encoded_bound (records : List BucketProgram.Record) (keys : List (List Bool))
    (T : ℕ) (hkeys : ∀ key ∈ keys, key.length ≤ T) :
    (ProgramEncoding.encodeRecords (table records keys)).length ≤
      1 + (2 * (2 * T + 1 + (BucketProgram.encodeRecords records).length) + 2) * keys.length := by
  simpa only [table, List.length_map] using
    ProgramEncoding.encodeRecords_length_le (table records keys)
      (2 * T + 1 + (BucketProgram.encodeRecords records).length)
      (table_payload_bound records keys T hkeys)

theorem iteration_bound (records : List BucketProgram.Record) (keys : List (List Bool))
    (T : ℕ) (hkeys : ∀ key ∈ keys, key.length ≤ T) :
    RecordPrograms.budget (callbackCost records) keys ≤
      keys.length * (6 * T + 100 * ((BucketProgram.encodeRecords records).length + 1) * (T + 1) + 7) := by
  induction keys with
  | nil => simp [RecordPrograms.budget]
  | cons key keys ih =>
    have hk := hkeys key (by simp)
    have ht := ih (fun q hq => hkeys q (by simp [hq]))
    have hc : callbackCost records key ≤
        100 * ((BucketProgram.encodeRecords records).length + 1) * (T + 1) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right hk 1)
    simp only [RecordPrograms.budget, List.length_cons, Nat.add_mul]
    omega

/-- Every factor here is a data length or a constant. In particular the
degree does not depend on the number of types or on the vertex count. -/
theorem budget_bound (records : List BucketProgram.Record) (keys : List (List Bool))
    (T : ℕ) (hkeys : ∀ key ∈ keys, key.length ≤ T) :
    budget records keys ≤
      9 + keys.length *
        (6 * T + 100 * ((BucketProgram.encodeRecords records).length + 1) * (T + 1) + 7) +
        3 * (1 + (2 * (2 * T + 1 + (BucketProgram.encodeRecords records).length) + 2) * keys.length) := by
  have hi := iteration_bound records keys T hkeys
  have ht := table_encoded_bound records keys T hkeys
  unfold budget
  omega

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
