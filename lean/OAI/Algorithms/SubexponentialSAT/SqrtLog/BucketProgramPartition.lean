import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramGrouping

namespace OAI.Algorithms

/-! Exhaustive, disjoint, duplicate-free attained buckets. These properties
are attached to the exact record table physically scanned by groupProgram. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

theorem bucketAssignments_nodup (records : List Record) (key : List Bool)
    (hn : (records.map Prod.snd).Nodup) : (bucketAssignments records key).Nodup := by
  induction records with
  | nil => simp [bucketAssignments,SubexponentialSAT.Subexp.BucketProgram.selected]
  | cons rec records ih =>
      rcases rec with ⟨k,p⟩
      have hn' : p ∉ records.map Prod.snd ∧ (records.map Prod.snd).Nodup := by simpa using hn
      have ht := ih hn'.2
      by_cases hk : k=key
      · have hp : p ∉ bucketAssignments records key := by
          intro hm
          have hmem := (mem_bucketAssignments records key p).mp hm
          exact hn'.1 (List.mem_map.mpr ⟨(key,p),hmem,rfl⟩)
        simpa [bucketAssignments,SubexponentialSAT.Subexp.BucketProgram.selected,hk] using List.nodup_cons.mpr ⟨hp,ht⟩
      · simpa [bucketAssignments,SubexponentialSAT.Subexp.BucketProgram.selected,hk] using ht

theorem bucketAssignments_disjoint (records : List Record) (key other : List Bool)
    (hn : (records.map Prod.snd).Nodup) (hne : key≠other) :
    List.Disjoint (bucketAssignments records key) (bucketAssignments records other) := by
  apply List.disjoint_left.mpr
  intro p hp hq
  have hp' := (mem_bucketAssignments records key p).mp hp
  have hq' := (mem_bucketAssignments records other p).mp hq
  have he := List.inj_on_of_nodup_map hn hp' hq' (show (key,p).2=(other,p).2 from rfl)
  exact hne (congrArg Prod.fst he)

theorem attained_buckets_exhaustive (records : List Record) (payload : List Bool) :
    payload ∈ records.map Prod.snd ↔
      ∃ key ∈ attainedKeys records, payload ∈ bucketAssignments records key := by
  constructor
  · intro hp
    obtain ⟨⟨key,p⟩,hm,he⟩ := List.mem_map.mp hp
    simp only at he
    subst p
    exact ⟨key,(mem_attainedKeys records key).mpr ⟨payload,hm⟩,
      (mem_bucketAssignments records key payload).mpr hm⟩
  · rintro ⟨key,hkey,hp⟩
    exact List.mem_map.mpr ⟨(key,payload),(mem_bucketAssignments records key payload).mp hp,rfl⟩

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
