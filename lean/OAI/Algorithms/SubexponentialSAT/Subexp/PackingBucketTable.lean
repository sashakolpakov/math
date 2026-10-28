import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketCalls

namespace OAI.Algorithms

/-! The fixed all-key bucket/minimum controller. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open BitProgram StructuredCalls MatrixProgramSupport PackingBucketCalls

def ports : RecordPrograms.Ports 8 15 :=
  ⟨5, 6, 7, 7, 2, by decide, by decide, by decide, by decide⟩

abbrev sequence (cs : List (Cmd 8 15)) : Cmd 8 15 :=
  cs.foldr Cmd.seq (.base .skip)

abbrev callback : Cmd 8 15 := sequence [
  MatrixProgramSupport.copy 6 0 12,
  bucketCall,
  MatrixProgramSupport.copy 5 9 12,
  countCall,
  minimumCall,
  move 14 10 12,
  transfer 2 9,
  emitFrame 9 5 12 (by decide),
  emitFrame 5 9 12 (by decide),
  TupleProgram.pushConst 9 0 true,
  transfer 9 11,
  .base (.atom (.set 5 false)),
  .base (.atom (.set 6 true)),
  .base (.atom (.set 7 false))]

abbrev command : Cmd 8 15 :=
  .seq (RecordPrograms.iterate ports callback)
    (.seq (TupleProgram.pushConst 11 0 false) (transfer 11 5))

def program := compiled command 7 5

def bucketPayload (records : List BucketProgram.Record) (key : List Bool) : List Bool :=
  Encoding.frame key ++ words (BucketProgram.selected records key)

def minimum (records : List BucketProgram.Record) (keys : List (List Bool)) (initial : ℕ) : ℕ :=
  keys.foldl (fun m key => min m (BucketProgram.selected records key).length) initial

def table (records : List BucketProgram.Record) (keys : List (List Bool)) : List (List Bool) :=
  keys.map (bucketPayload records)

def callbackCost (records : List BucketProgram.Record) (key : List Bool) : ℕ :=
  100 * ((BucketProgram.encodeRecords records).length + 1) * (key.length + 1)

def budget (records : List BucketProgram.Record) (keys : List (List Bool)) : ℕ :=
  6 + RecordPrograms.budget (callbackCost records) keys +
    3 * (ProgramEncoding.encodeRecords (table records keys)).length + 3

theorem selected_length_le (records : List BucketProgram.Record) (key : List Bool) :
    (BucketProgram.selected records key).length ≤ records.length := by
  induction records with
  | nil => simp [BucketProgram.selected]
  | cons row rows ih =>
    rcases row with ⟨k, payload⟩
    by_cases hk : k = key <;> simp [BucketProgram.selected, hk] <;> omega

theorem selected_words_length_le (records : List BucketProgram.Record) (key : List Bool) :
    (words (BucketProgram.selected records key)).length ≤
      (BucketProgram.encodeRecords records).length := by
  induction records with
  | nil => simp [BucketProgram.selected, words, BucketProgram.encodeRecords]
  | cons row rows ih =>
    rcases row with ⟨k, payload⟩
    by_cases hk : k = key <;>
      simp [BucketProgram.selected, hk, words, BucketProgram.encodeRecords,
        Encoding.length_frame] <;> omega

theorem minimum_le (records : List BucketProgram.Record) (keys : List (List Bool)) (initial : ℕ) :
    minimum records keys initial ≤ initial := by
  induction keys generalizing initial with
  | nil => exact le_rfl
  | cons key keys ih =>
    exact (ih _).trans (min_le_left _ _)

theorem encodeRecords_length_reverse (records : List BucketProgram.Record) :
    (BucketProgram.encodeRecords records.reverse).length =
      (BucketProgram.encodeRecords records).length := by
  have hlen (xs : List BucketProgram.Record) :
      (BucketProgram.encodeRecords xs).length =
        (xs.map fun p => 2 * p.1.length + 2 * p.2.length + 2).sum := by
    induction xs with
    | nil => rfl
    | cons p xs ih =>
      rcases p with ⟨key, value⟩
      simp only [BucketProgram.encodeRecords, List.length_append, Encoding.length_frame,
        List.map_cons, List.sum_cons, ih]
      omega
  rw [hlen, List.map_reverse, List.sum_reverse, hlen]

/-- The actual subroutine costs fit one uniform bound in the encoded table
and query lengths. The minimum never exceeds its current unary cap. -/
theorem callback_arithmetic (L q m n B scan : ℕ)
    (hm : m ≤ L) (hn : n ≤ L) (hB : B ≤ L)
    (hs : scan ≤ 9 * L + L * (9 * q + 20) + 3) :
    (7 * L + 5) + (scan + ((7 * B + 5) + ((11 * B + 3) +
      ((9 * (m + n) + 12) + ((6 * min m n + 6) + ((3 * q + 3) +
        ((8 * q + 8) + ((8 * (2 * q + 1 + B) + 8) +
          (2 + ((3 * (2 * (2 * q + 1 + B) + 2) + 3) + 3)))))))))) ≤
      100 * (L + 1) * (q + 1) := by
  have hmin : min m n ≤ L := (min_le_left _ _).trans hm
  ring_nf at *
  omega

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
