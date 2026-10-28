import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramLabelLoop
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramEnumeration
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramPartition
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramSignatureSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgramTyped

namespace OAI.Algorithms

/-! Exact exhaustive head partition represented by the physically emitted
label table. Ambient masks retain all n positions, including unused ones. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram
open HeadScatterProgram

variable {n h k : ℕ}

theorem mask_injective_on_assignments (head : Fin h → Fin n)
    (hinj : Function.Injective head) :
    Set.InjOn (fun bits => mask n (headIds head) bits) {bits | bits∈assignments h} := by
  intro a ha b hb he
  obtain ⟨x,rfl⟩ := assignments_sound ha
  obtain ⟨y,rfl⟩ := assignments_sound hb
  have hx : x=y := typed_mask_injective head hinj he
  subst y
  rfl

theorem labelled_payloads_nodup (head : Fin h → Fin n) (hinj : Function.Injective head)
    (W : List Bool) (rows : List (List (List Bool))) :
    ((Label.labelled W rows (headIds head) n (assignments h)).map Prod.snd).Nodup := by
  have hm := (assignments_nodup h).map_on (mask_injective_on_assignments head hinj)
  simpa [Label.labelled,List.map_map,Function.comp_def] using hm

theorem generated_buckets_nodup (head : Fin h → Fin n) (hinj : Function.Injective head)
    (W : List Bool) (rows : List (List (List Bool))) (key : List Bool) :
    (bucketAssignments (Label.labelled W rows (headIds head) n (assignments h)) key).Nodup :=
  bucketAssignments_nodup _ _ (labelled_payloads_nodup head hinj W rows)

theorem generated_assignment_stored (head : Fin h → Fin n) (W : List Bool)
    (rows : List (List (List Bool))) (x : Fin h → Bool) :
    (Label.key W (List.ofFn x) rows,mask n (headIds head) (List.ofFn x)) ∈
      Label.labelled W rows (headIds head) n (assignments h) := by
  exact List.mem_map.mpr ⟨List.ofFn x,assignments_complete x,rfl⟩

theorem generated_assignment_covered (head : Fin h → Fin n) (W : List Bool)
    (rows : List (List (List Bool))) (x : Fin h → Bool) :
    ∃ key ∈ attainedKeys (Label.labelled W rows (headIds head) n (assignments h)),
      mask n (headIds head) (List.ofFn x) ∈
        bucketAssignments (Label.labelled W rows (headIds head) n (assignments h)) key := by
  have hm := generated_assignment_stored head W rows x
  exact ⟨_,(mem_attainedKeys _ _).mpr ⟨_,hm⟩,(mem_bucketAssignments _ _ _).mpr hm⟩

theorem generated_bucket_exact (head : Fin h → Fin n) (hinj : Function.Injective head)
    (W : List Bool) (c : Fin k → Fin h → List Bool) (A : Fin k → Fin h → ℤ)
    (x y : Fin h → Bool)
    (hc : ∀ j i, (SubexponentialSAT.BinaryArithmetic.toNat (c j i) : ℤ) =
      (SubexponentialSAT.BinaryArithmetic.toNat W : ℤ)+A j i) :
    mask n (headIds head) (List.ofFn y) ∈
      bucketAssignments (Label.labelled W (List.ofFn (fun j => List.ofFn (c j)))
        (headIds head) n (assignments h))
        (Label.key W (List.ofFn x) (List.ofFn (fun j => List.ofFn (c j)))) ↔
    ∀ j, (∑ i, A j i*(if x i then 1 else 0)) =
      (∑ i, A j i*(if y i then 1 else 0)) := by
  rw [mem_bucketAssignments]
  constructor
  · intro hm
    obtain ⟨bits,hbits,he⟩ := List.mem_map.mp hm
    obtain ⟨z,rfl⟩ := assignments_sound hbits
    have hz : z=y := typed_mask_injective head hinj (congrArg Prod.snd he)
    subst z
    apply (signatureValue_exact_iff W c A x y hc).mp
    exact (congrArg Prod.fst he).symm
  · intro he
    have hs := (signatureValue_exact_iff W c A x y hc).mpr he
    have hm := generated_assignment_stored head W (List.ofFn (fun j => List.ofFn (c j))) y
    simpa only [Label.key,←hs] using hm

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
