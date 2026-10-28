import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceControls

namespace OAI.Algorithms

/-! Byte-level value and frame rules for source preparation. These rules
concern the actual paid copy/clear state transformer, not assumed source
execution or a supplied readiness certificate. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
abbrev Data := State 16 768

def prepared (a : Data) : Data := SourceControls.prepared (SourceStaging.saved a)
def localPort (i : Fin 340) : Fin 768 := ⟨340+i.val,by omega⟩
def localStore (a : Data) : Fin 340 → List Bool := (prepared a).stacks ∘ localPort

theorem saved_frame (a : Data) (i : Fin 768)
    (hc : i ∉ SourceStaging.cachePorts) (hb : i ∉ SourceStaging.backupPorts) :
    (SourceStaging.saved a).stacks i = a.stacks i := by
  rw [SourceStaging.saved,clearMany_stacks,ite_eq_right hc]
  apply copyMany_frame
  intro p hp he
  have hm : p.2 ∈ SourceStaging.backupPorts := by
    simp only [SourceStaging.savePairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl <;> decide
  exact hb (he.symm ▸ hm)

theorem prepared_frame (a : Data) (i : Fin 768)
    (h365 : i ≠ 365) (hp : ∀ p ∈ SourceControls.pairs,i ≠ p.2)
    (hc : i ∉ SourceStaging.cachePorts) (hb : i ∉ SourceStaging.backupPorts) :
    (prepared a).stacks i = a.stacks i := by
  unfold prepared SourceControls.prepared
  rw [SourceControls.delta_stacks,Function.update_of_ne h365,copyMany_frame _ _ _ hp]
  exact saved_frame a i hc hb

theorem prepared_copy (a : Data)
    (he : ∀ p ∈ SourceControls.pairs,a.stacks p.2=[])
    (p : Fin 768 × Fin 768) (hp : p ∈ SourceControls.pairs) :
    (prepared a).stacks p.2 = a.stacks p.1 := by
  have hs : ∀ q ∈ SourceControls.pairs,
      q.1 ∉ SourceStaging.cachePorts ∧ q.1 ∉ SourceStaging.backupPorts ∧
      q.2 ∉ SourceStaging.cachePorts ∧ q.2 ∉ SourceStaging.backupPorts ∧ q.2 ≠ 365 := by
    simp [SourceControls.pairs,SourceStaging.cachePorts,SourceStaging.backupPorts]
  have hz : ∀ q ∈ SourceControls.pairs,(SourceStaging.saved a).stacks q.2=[] := by
    intro q hq
    rw [saved_frame a q.2 (hs q hq).2.2.1 (hs q hq).2.2.2.1]
    exact he q hq
  unfold prepared SourceControls.prepared
  rw [SourceControls.delta_stacks,Function.update_of_ne (hs p hp).2.2.2.2]
  rw [copyMany_value SourceControls.pairs (SourceStaging.saved a)
    (by decide) hz (by simp [SourceControls.pairs]) p hp]
  exact saved_frame a p.1 (hs p hp).1 (hs p hp).2.1

theorem prepared_cache (a : Data) (i : Fin 768) (hi : i ∈ SourceStaging.cachePorts) :
    (prepared a).stacks i=[] := by
  have h365 : i ≠ 365 := by
    simp only [SourceStaging.cachePorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> decide
  have hp : ∀ p ∈ SourceControls.pairs,i ≠ p.2 := by
    simp only [SourceStaging.cachePorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> simp [SourceControls.pairs]
  unfold prepared SourceControls.prepared
  rw [SourceControls.delta_stacks,Function.update_of_ne h365,copyMany_frame _ _ _ hp]
  exact SourceStaging.saved_empty a i hi

theorem prepared_delta (a : Data) (he : a.stacks 365=[]) :
    (prepared a).stacks 365=[true] := by
  unfold prepared SourceControls.prepared
  rw [SourceControls.delta_stacks,Function.update_same,
    copyMany_frame SourceControls.pairs _ 365 (by simp [SourceControls.pairs]),
    saved_frame a 365 (by decide) (by decide),he]

/-- Exactly the local stacks changed by source preparation. -/
def changedLocal : List (Fin 340) :=
  [21,22,25,26,42,43,44,45,47,48,192,193,242,243,249,250,251,252,
   306,308,309,310,311,312,313,314,337]

private theorem localPort_ne_delta (i : Fin 340) (hi : i ∉ changedLocal) :
    localPort i ≠ 365 := by
  intro h
  have hv := congrArg Fin.val h
  simp [localPort] at hv
  simp [changedLocal] at hi
  omega

private theorem localPort_not_cache (i : Fin 340) (hi : i ∉ changedLocal) :
    localPort i ∉ SourceStaging.cachePorts := by
  intro h
  simp [SourceStaging.cachePorts] at h
  rcases h with h | h | h | h <;>
    have hv := congrArg Fin.val h <;>
    simp [localPort] at hv <;>
    simp [changedLocal] at hi <;>
    omega

private theorem localPort_not_backup (i : Fin 340) :
    localPort i ∉ SourceStaging.backupPorts := by
  intro h
  simp [SourceStaging.backupPorts] at h
  rcases h with h | h | h | h <;>
    have hv := congrArg Fin.val h <;>
    simp [localPort] at hv <;>
    omega

theorem local_frame (a : Data) (i : Fin 340) (hi : i ∉ changedLocal) :
    localStore a i = a.stacks (localPort i) := by
  apply prepared_frame
  · exact localPort_ne_delta i hi
  · intro p hp
    simp only [SourceControls.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      intro h
      have hv := congrArg Fin.val h
      simp [localPort] at hv
      simp [changedLocal] at hi
      omega
  · exact localPort_not_cache i hi
  · exact localPort_not_backup i

theorem local_copy (a : Data)
    (he : ∀ p ∈ SourceControls.pairs,a.stacks p.2=[])
    (src : Fin 768) (dst : Fin 340) (hp : (src,localPort dst) ∈ SourceControls.pairs) :
    localStore a dst = a.stacks src := prepared_copy a he _ hp

theorem local_cache (a : Data) (i : Fin 340)
    (hi : i ∈ ([192,193,242,243] : List (Fin 340))) : localStore a i=[] := by
  apply prepared_cache
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [localPort, SourceStaging.cachePorts]

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
