import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramSchema
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramControllerGroup

namespace OAI.Algorithms

/-! Derive the logical bucket list from the actual per-head controller output.
No already-grouped bucket witness is supplied by the caller. -/
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram

open SubexponentialSAT.SqrtLog.BucketProgram
open SubexponentialSAT.SqrtLog.MomentsAssembly (HeadInput)

def controllerBuckets (records : List Record) : List Table.Bucket :=
  (Controller.keys records).map fun key => (key,bucketAssignments records key)

theorem controllerBuckets_bytes (records : List Record) :
    Table.tableBits (controllerBuckets records) = Controller.tableOutput records := by
  exact tableBits_attained records (Controller.keys records)

theorem controller_key_attained (records : List Record) (key : List Bool)
    (hk : key∈Controller.keys records) : key∈attainedKeys records := by
  simpa only [Controller.keys,mem_attainedKeys,List.mem_reverse] using hk

theorem controllerBuckets_nonempty (records : List Record) (b : Table.Bucket)
    (hb : b∈controllerBuckets records) : b.2≠[] := by
  obtain ⟨key,hkey,rfl⟩ := List.mem_map.mp hb
  exact attained_bucket_nonempty records key (controller_key_attained records key hkey)

theorem controllerBuckets_width (records : List Record) (n : ℕ)
    (hw : ∀ rec∈records,rec.2.length=n) (b : Table.Bucket)
    (hb : b∈controllerBuckets records) : ∀ assignment∈b.2,assignment.length=n := by
  obtain ⟨key,hkey,rfl⟩ := List.mem_map.mp hb
  intro assignment ha
  exact hw (key,assignment) ((mem_bucketAssignments records key assignment).mp ha)

theorem labelledRecords_width (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) (hjs : ∀ j∈js,j < n) :
    ∀ rec∈Controller.labelledRecords W rows js n h,rec.2.length=n := by
  intro rec hr
  obtain ⟨bits,hbits,rfl⟩ := List.mem_map.mp hr
  exact HeadScatterProgram.mask_length n js bits hjs

def actualBuckets (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) : List Table.Bucket :=
  controllerBuckets (Controller.labelledRecords W rows js n h)

/-- Even an empty head has its empty assignment and hence an attained bucket. -/
theorem actualBuckets_length_pos (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) : 0 < (actualBuckets W rows js n h).length := by
  let bits := List.ofFn (fun _ : Fin h => false)
  let records := Controller.labelledRecords W rows js n h
  let witnessRecord : Record := (Label.key W bits rows,HeadScatterProgram.mask n js bits)
  have hr : witnessRecord ∈ records := by
    exact List.mem_map.mpr ⟨bits,assignments_complete (fun _ : Fin h => false),rfl⟩
  have hk : witnessRecord.1 ∈ Controller.keys records := by
    apply (mem_attainedKeys records.reverse witnessRecord.1).mpr
    exact ⟨witnessRecord.2,by simpa only [List.mem_reverse] using hr⟩
  have hb : (witnessRecord.1,bucketAssignments records witnessRecord.1) ∈
      actualBuckets W rows js n h :=
    List.mem_map.mpr ⟨witnessRecord.1,hk,rfl⟩
  cases he : actualBuckets W rows js n h with
  | nil => rw [he] at hb; exact (List.not_mem_nil hb).elim
  | cons b bs => exact Nat.zero_lt_succ _

theorem actualBuckets_bytes (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) :
    Table.tableBits (actualBuckets W rows js n h) =
      Controller.tableOutput (Controller.labelledRecords W rows js n h) :=
  controllerBuckets_bytes _

theorem actualBuckets_nonempty (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) (b : Table.Bucket) (hb : b∈actualBuckets W rows js n h) :
    b.2≠[] := controllerBuckets_nonempty _ b hb

theorem actualBuckets_width (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) (hjs : ∀ j∈js,j < n) (b : Table.Bucket)
    (hb : b∈actualBuckets W rows js n h) : ∀ assignment∈b.2,assignment.length=n :=
  controllerBuckets_width _ n (labelledRecords_width W rows js n h hjs) b hb

theorem actualBuckets_valid (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) (hjs : ∀ j∈js,j < n)
    (mask context : List Bool) (hm : mask.length=n) (b : Table.Bucket)
    (hb : b∈actualBuckets W rows js n h) :
    Representative.Valid n (⟨mask,context,b.2⟩ : HeadInput) := by
  have hne := actualBuckets_nonempty W rows js n h b hb
  cases he : b.2 with
  | nil => exact (hne he).elim
  | cons rep rest =>
      refine ⟨rep,rest,rfl,?_,hm⟩
      exact actualBuckets_width W rows js n h hjs b hb rep (by simp [he])

end SubexponentialSAT.SqrtLog.BucketTupleProgram

end OAI.Algorithms
