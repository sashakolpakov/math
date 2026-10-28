import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramController

namespace OAI.Algorithms

/-! Every emitted group is attained, and every enumerated head occurs in
its exact-signature bucket. This interface follows the actual reversed key
order used by the fixed controller. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.Controller

@[simp] theorem mem_keys (records : List Record) (key : List Bool) :
    key ∈ keys records ↔ ∃ payload, (key,payload) ∈ records := by
  simp [keys,mem_attainedKeys]

theorem keys_nodup (records : List Record) : (keys records).Nodup :=
  attainedKeys_nodup records.reverse

theorem keys_length_le (records : List Record) : (keys records).length ≤ records.length := by
  simpa [keys] using attainedKeys_length_le records.reverse

theorem key_bucket_nonempty (records : List Record) (key : List Bool)
    (hk : key ∈ keys records) : bucketAssignments records key ≠ [] := by
  obtain ⟨payload,hp⟩ := (mem_keys records key).mp hk
  intro he
  have hm := (mem_bucketAssignments records key payload).mpr hp
  simp [he] at hm

@[simp] theorem labelledRecords_length (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) : (labelledRecords W rows js n h).length=2^h := by
  simp [labelledRecords,Label.labelled]

theorem head_in_its_bucket (W bits : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) (hb : bits∈assignments h) :
    Label.key W bits rows ∈ keys (labelledRecords W rows js n h) ∧
    HeadScatterProgram.mask n js bits ∈
      bucketAssignments (labelledRecords W rows js n h) (Label.key W bits rows) := by
  have hm : (Label.key W bits rows,HeadScatterProgram.mask n js bits) ∈
      labelledRecords W rows js n h := List.mem_map.mpr ⟨bits,hb,rfl⟩
  exact ⟨(mem_keys _ _).mpr ⟨_,hm⟩,(mem_bucketAssignments _ _ _).mpr hm⟩

theorem every_bucket_head (W key payload : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ)
    (hp : payload∈bucketAssignments (labelledRecords W rows js n h) key) :
    ∃ bits∈assignments h, Label.key W bits rows=key ∧ HeadScatterProgram.mask n js bits=payload := by
  have hm := (mem_bucketAssignments _ _ _).mp hp
  obtain ⟨bits,hb,he⟩ := List.mem_map.mp hm
  exact ⟨bits,hb,Prod.mk.inj he⟩

end SubexponentialSAT.SqrtLog.BucketProgram.Controller

end OAI.Algorithms
