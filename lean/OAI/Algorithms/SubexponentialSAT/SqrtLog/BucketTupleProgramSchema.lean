import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramExpand
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramFinalize
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketTable

namespace OAI.Algorithms

/-! Semantic bridge: the physical Cartesian alphabet consists of whole attained
buckets. Its cardinality is the product of attained bucket counts. -/
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram

open SubexponentialSAT.SqrtLog.MomentsAssembly (HeadInput rawFrames)
open Representative (headsBits)

structure HeadTable where
  mask : List Bool
  context : List Bool
  buckets : List Table.Bucket

def HeadTable.choices (h : HeadTable) : List HeadInput :=
  (h.buckets.map fun b => ⟨h.mask,h.context,b.2⟩).reverse

def extend (rows : List (List HeadInput)) (choices : List HeadInput) : List (List HeadInput) :=
  (rows.flatMap fun row => choices.map fun h => row++[h]).reverse

def enumerateFrom : List HeadTable → List (List HeadInput) → List (List HeadInput)
  | [], rows => rows
  | h::hs,rows => enumerateFrom hs (extend rows h.choices)

def enumerate (heads : List HeadTable) : List (List HeadInput) := enumerateFrom heads [[]]

theorem headBits_eq (mask context : List Bool) (b : Table.Bucket) :
    (HeadInput.bits ⟨mask,context,b.2⟩) = Table.headBits mask context b := by
  simp [HeadInput.bits,Table.headBits,Representative.rawFrames_eq_words]

theorem alphabet_eq (h : HeadTable) :
    Expand.alphabet h.mask h.context h.buckets =
      h.choices.map (fun x => Encoding.frame x.bits) := by
  simp [Expand.alphabet,HeadTable.choices,List.map_reverse,List.map_map,
    Table.alphabetWord,headBits_eq,Function.comp_def]

theorem tuplesBits_eq (tuples : List (List HeadInput)) :
    Representative.tuplesBits tuples =
      ProgramEncoding.encodeRecords (tuples.map headsBits) := by
  induction tuples with
  | nil => rfl
  | cons hs tuples ih =>
      simpa [Representative.tuplesBits,ProgramEncoding.encodeRecords,Encoding.encodeList] using
        congrArg (fun tail => true :: (Encoding.frame (headsBits hs)++tail)) ih

theorem headsBits_append (a b : List HeadInput) :
    headsBits (a++b)=headsBits a++headsBits b := by
  simp [headsBits,List.map_append,Representative.rawFrames_eq_words,
    SubexponentialSAT.Subexp.MatrixProgramSupport.words_append]

theorem headsBits_singleton (h : HeadInput) : headsBits [h]=Encoding.frame h.bits := by
  simp [headsBits,rawFrames]

theorem extend_bits (rows : List (List HeadInput)) (choices : List HeadInput) :
    (extend rows choices).map headsBits = SubexponentialSAT.Subexp.TupleProgram.cartesianOutput
      (rows.map headsBits) (choices.map fun h => Encoding.frame h.bits) := by
  simp [extend,SubexponentialSAT.Subexp.TupleProgram.cartesianOutput,List.map_reverse,List.map_flatMap,
    List.flatMap_map,List.map_map,Function.comp_def,headsBits_append,headsBits_singleton]

theorem nextRows_eq (rows : List (List HeadInput)) (h : HeadTable) :
    Expand.nextRows (rows.map headsBits) h.mask h.context h.buckets =
      (extend rows h.choices).map headsBits := by
  rw [extend_bits,Expand.nextRows,alphabet_eq]

theorem extend_length (rows : List (List HeadInput)) (choices : List HeadInput) :
    (extend rows choices).length=rows.length*choices.length := by
  simp only [extend,List.length_reverse]
  induction rows with
  | nil => simp
  | cons row rows ih => simp [ih,Nat.add_mul,Nat.add_comm]

theorem choices_length (h : HeadTable) : h.choices.length=h.buckets.length := by
  simp [HeadTable.choices]

theorem enumerateFrom_length (heads : List HeadTable) (rows : List (List HeadInput)) :
    (enumerateFrom heads rows).length = rows.length*(heads.map fun h=>h.buckets.length).prod := by
  induction heads generalizing rows with
  | nil => simp [enumerateFrom]
  | cons h hs ih => simp [enumerateFrom,ih,extend_length,choices_length,Nat.mul_assoc]

theorem enumerate_length (heads : List HeadTable) :
    (enumerate heads).length=(heads.map fun h=>h.buckets.length).prod := by
  simp [enumerate,enumerateFrom_length]

/-- Direct equality with the producer's emitted table: no runtime conversion
from individual assignments to singleton buckets is inserted. -/
theorem tableBits_attained (records : List SubexponentialSAT.Subexp.BucketProgram.Record)
    (keys : List (List Bool)) :
    Table.tableBits (keys.map fun key => (key,SubexponentialSAT.Subexp.BucketProgram.selected records key)) =
      ProgramEncoding.encodeRecords (SubexponentialSAT.Subexp.PackingBucketTable.table records keys) := by
  simp only [Table.tableBits,SubexponentialSAT.Subexp.PackingBucketTable.table,
ProgramEncoding.encodeRecords]
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      simpa [Encoding.encodeList,Table.payload,SubexponentialSAT.Subexp.PackingBucketTable.bucketPayload] using congrArg
        (fun rest => true :: (Encoding.frame (Encoding.frame key ++
          SubexponentialSAT.Subexp.MatrixProgramSupport.words (SubexponentialSAT.Subexp.BucketProgram.selected records key))++rest)) ih

/-- Every final head came from one whole attained bucket for its head. -/
theorem extend_valid (n : ℕ) (rows : List (List HeadInput)) (choices : List HeadInput)
    (hr : ∀ row∈rows,∀ h∈row,Representative.Valid n h)
    (hc : ∀ h∈choices,Representative.Valid n h) :
    ∀ row∈extend rows choices,∀ h∈row,Representative.Valid n h := by
  intro row hrow h hh
  simp only [extend,List.mem_reverse,List.mem_flatMap,List.mem_map] at hrow
  obtain ⟨old,hold,new,hnew,rfl⟩ := hrow
  rcases List.mem_append.mp hh with hOld|hNew
  · exact hr old hold h hOld
  · have he : h = new := by simpa using hNew
    subst h
    exact hc new hnew

theorem choices_valid (n : ℕ) (table : HeadTable)
    (hv : ∀ b∈table.buckets,Representative.Valid n
      (⟨table.mask,table.context,b.2⟩ : HeadInput)) :
    ∀ h∈table.choices,Representative.Valid n h := by
  intro h hh
  simp only [HeadTable.choices,List.mem_reverse,List.mem_map] at hh
  obtain ⟨b,hb,rfl⟩ := hh
  exact hv b hb

theorem nextRows_valid (n : ℕ) (rows : List (List HeadInput)) (table : HeadTable)
    (hr : ∀ row∈rows,∀ h∈row,Representative.Valid n h)
    (hb : ∀ b∈table.buckets,Representative.Valid n
      (⟨table.mask,table.context,b.2⟩ : HeadInput)) :
    ∀ row∈extend rows table.choices,∀ h∈row,Representative.Valid n h :=
  extend_valid n rows table.choices hr (choices_valid n table hb)

theorem enumerateFrom_valid (n : ℕ) (tables : List HeadTable) (rows : List (List HeadInput))
    (ht : ∀ table∈tables,∀ b∈table.buckets,Representative.Valid n
      (⟨table.mask,table.context,b.2⟩ : HeadInput))
    (hr : ∀ row∈rows,∀ h∈row,Representative.Valid n h) :
    ∀ row∈enumerateFrom tables rows,∀ h∈row,Representative.Valid n h := by
  induction tables generalizing rows with
  | nil => exact hr
  | cons table tables ih =>
      exact ih (extend rows table.choices) (fun t ht' => ht t (by simp [ht']))
        (nextRows_valid n rows table hr (ht table (by simp)))

theorem enumerate_valid (n : ℕ) (tables : List HeadTable)
    (ht : ∀ table∈tables,∀ b∈table.buckets,Representative.Valid n
      (⟨table.mask,table.context,b.2⟩ : HeadInput)) :
    ∀ row∈enumerate tables,∀ h∈row,Representative.Valid n h :=
  enumerateFrom_valid n tables [[]] ht (by simp)

end SubexponentialSAT.SqrtLog.BucketTupleProgram

end OAI.Algorithms
