import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecLiteralDedupProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketExecution
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketBounds

namespace OAI.Algorithms

/-! Concrete byte-string deduplication and all-key bucket scans. This file
starts at the explicit labelled-record table, not at an uncharged signature
oracle. Producing that table is the separate dot-product stage. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Record := SubexponentialSAT.Subexp.BucketProgram.Record

def attainedKeys (records : List Record) : List (List Bool) :=
  SubexponentialSAT.ExecCNF.dedupLiterals (records.map Prod.fst)

def bucketAssignments (records : List Record) (key : List Bool) : List (List Bool) :=
  SubexponentialSAT.Subexp.BucketProgram.selected records key

@[simp] theorem mem_attainedKeys (records : List Record) (key : List Bool) :
    key ∈ attainedKeys records ↔ ∃ payload, (key,payload) ∈ records := by
  simp only [attainedKeys, SubexponentialSAT.ExecCNF.mem_dedupLiterals, List.mem_map]
  constructor
  · rintro ⟨⟨k,p⟩, hm, he⟩; simp only at he; subst k; exact ⟨p, hm⟩
  · rintro ⟨p, hp⟩; exact ⟨(key,p), hp, rfl⟩

theorem attainedKeys_nodup (records : List Record) : (attainedKeys records).Nodup :=
  SubexponentialSAT.ExecCNF.dedupLiterals_nodup _

theorem attainedKeys_length_le (records : List Record) :
    (attainedKeys records).length ≤ records.length := by
  simpa [attainedKeys] using SubexponentialSAT.ExecCNF.dedupLiterals_length_le (records.map Prod.fst)

@[simp] theorem mem_bucketAssignments (records : List Record) (key payload : List Bool) :
    payload ∈ bucketAssignments records key ↔ (key,payload) ∈ records := by
  induction records with
  | nil => simp [bucketAssignments, SubexponentialSAT.Subexp.BucketProgram.selected]
  | cons rec records ih =>
      rcases rec with ⟨k,p⟩
      by_cases hk : k=key
      · subst k
        simp [bucketAssignments, SubexponentialSAT.Subexp.BucketProgram.selected] at ih ⊢
        exact or_congr Iff.rfl ih
      · simp [bucketAssignments, SubexponentialSAT.Subexp.BucketProgram.selected, hk] at ih ⊢
        simpa [Prod.mk.injEq, hk, Ne.symm hk] using ih

theorem attained_bucket_nonempty (records : List Record) (key : List Bool)
    (hk : key ∈ attainedKeys records) : bucketAssignments records key ≠ [] := by
  obtain ⟨p,hp⟩ := (mem_attainedKeys records key).mp hk
  intro he
  have hm := (mem_bucketAssignments records key p).mpr hp
  simp [he] at hm

/-- A representative can always be read as the first stored assignment.
The machine output stores every assignment, so this needs no choice oracle. -/
theorem attained_bucket_representative (records : List Record) (key : List Bool)
    (hk : key ∈ attainedKeys records) :
    ∃ rep rest, bucketAssignments records key = rep::rest ∧ (key,rep) ∈ records := by
  cases he : bucketAssignments records key with
  | nil => exact (attained_bucket_nonempty records key hk he).elim
  | cons rep rest =>
      refine ⟨rep,rest,rfl,?_⟩
      exact (mem_bucketAssignments records key rep).mp (by simp [he])

abbrev keyDedupProgram := SubexponentialSAT.ExecLiteralDedupProgram.dedupProgram

/-- Actual key deduplication, with quadratic measured encoded-input cost. -/
theorem keyDedup_runsIn (records : List Record) (d : SubexponentialSAT.ExecLiteralDedupProgram.Data)
    (hs : d.stacks 0 = ProgramEncoding.encodeRecords (records.map Prod.fst))
    (hr : SubexponentialSAT.ExecLiteralDedupProgram.Ready d) :
    ∃ e, SubexponentialSAT.ExecLiteralDedupProgram.Ready e ∧
      e.stacks 0 = ProgramEncoding.encodeRecords (attainedKeys records) ∧
      RunsIn keyDedupProgram
        (120*((ProgramEncoding.encodeRecords (records.map Prod.fst)).length+1)^2)
        (d.withPC (some keyDedupProgram.entry)) (e.withPC none) := by
  exact SubexponentialSAT.ExecLiteralDedupProgram.dedup_runsIn (records.map Prod.fst) d hs hr

abbrev groupProgram := SubexponentialSAT.Subexp.PackingBucketTable.program

def groupedTable (records : List Record) : List (List Bool) :=
  SubexponentialSAT.Subexp.PackingBucketTable.table records (attainedKeys records)

/-- One fixed all-key controller executes actual byte comparisons and emits
all attained buckets. The initial unary minimum is zero and remains zero;
its otherwise-unused legacy accumulator costs are included in the budget. -/
theorem groupProgram_trace (records : List Record) (regs : Fin 8 → Bool) :
    ∃ t ≤ SubexponentialSAT.Subexp.PackingBucketTable.budget records (attainedKeys records), ∃ rf,
      Trace groupProgram t
        ((SubexponentialSAT.Subexp.PackingBucketTable.inputState records (attainedKeys records) 0 [] regs).withPC
          (some groupProgram.entry))
        ((SubexponentialSAT.Subexp.PackingBucketTable.outputState records (attainedKeys records) 0 [] rf).withPC none) :=
  SubexponentialSAT.Subexp.PackingBucketTable.program_trace records (attainedKeys records) 0 (Nat.zero_le _) [] regs

/-- Each record and query is scanned; all resulting costs are polynomial
in the explicit table length and the number of attained keys. -/
theorem groupProgram_budget (records : List Record) (K : ℕ)
    (hk : ∀ rec ∈ records, rec.1.length ≤ K) :
    SubexponentialSAT.Subexp.PackingBucketTable.budget records (attainedKeys records) ≤
      9 + records.length *
        (6*K+100*((SubexponentialSAT.Subexp.BucketProgram.encodeRecords records).length+1)*(K+1)+7) +
        3*(1+(2*(2*K+1+(SubexponentialSAT.Subexp.BucketProgram.encodeRecords records).length)+2)*records.length) := by
  have hkeys : ∀ key ∈ attainedKeys records, key.length ≤ K := by
    intro key hkey
    obtain ⟨p,hp⟩ := (mem_attainedKeys records key).mp hkey
    exact hk (key,p) hp
  have hb := SubexponentialSAT.Subexp.PackingBucketTable.budget_bound records (attainedKeys records) K hkeys
  have hl := attainedKeys_length_le records
  exact hb.trans (by gcongr)

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
