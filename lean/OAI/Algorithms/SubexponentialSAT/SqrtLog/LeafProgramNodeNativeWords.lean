import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeInputs

namespace OAI.Algorithms

/-! Exact words and cleared scratch obtained from the actual preparation. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeNative
open SubexponentialSAT BitProgram StructuredCalls LeafHeadSetupProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem copy_target_cache (q : Fin 768 × Fin 768)
    (hq : q∈LeafNodeCacheProgram.directCopies) : q.2∈LeafNodeCacheProgram.cachePorts := by
  simp only [LeafNodeCacheProgram.directCopies,List.mem_cons,List.mem_nil_iff,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [LeafNodeCacheProgram.cachePorts]

private theorem copy_source_external (q : Fin 768 × Fin 768)
    (hq : q∈LeafNodeCacheProgram.directCopies) : External q.1 := by
  simp only [LeafNodeCacheProgram.directCopies,List.mem_cons,List.mem_nil_iff,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [External,Fin.ext_iff]

theorem Preparation.direct_word {s : HeadInputs} {a d : Data} (p : Preparation s a d)
    (ha : Ready s a) (q : Fin 768 × Fin 768) (hq : q∈LeafNodeCacheProgram.directCopies) :
    d.stacks q.2=(loadedState a).stacks q.1 := by
  have hn : q.2≠169 := by
    have hm := copy_target_cache q hq
    simp only [LeafNodeCacheProgram.cachePorts,List.mem_cons,List.mem_nil_iff,or_false] at hm
    rcases hm with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp [h]
  rw [p.support_frame _ hn,p.cached_words,
    LeafNodeCacheProgram.cache_direct _ (head_cache_ready s ha p.loaded_words p.head) q hq]
  change p.headEnd.stacks q.1=(loadedState a).stacks q.1
  rw [p.head.frame _ (copy_source_external q hq),p.loaded_words]

theorem Preparation.one_word {s : HeadInputs} {a d : Data} (p : Preparation s a d)
    (_ha : Ready s a) : d.stacks 69=LeafNodeCacheProgram.rawOne (loadedState a).stacks ∧
      d.stacks 167=LeafNodeCacheProgram.rawOne (loadedState a).stacks := by
  have h128 : p.headEnd.stacks 128=(loadedState a).stacks 128 :=
    (p.head.frame 128 (by norm_num [External,Fin.ext_iff])).trans (congrFun p.loaded_words 128)
  have h207 : p.headEnd.stacks 207=(loadedState a).stacks 207 :=
    (p.head.frame 207 (by norm_num [External,Fin.ext_iff])).trans (congrFun p.loaded_words 207)
  constructor
  · rw [p.support_frame 69 (by decide),p.cached_words,(LeafNodeCacheProgram.cache_one _).1]
    change LeafNodeCacheProgram.rawOne p.headEnd.stacks=_
    simp only [LeafNodeCacheProgram.rawOne,h128,h207]
  · rw [p.support_frame 167 (by decide),p.cached_words,(LeafNodeCacheProgram.cache_one _).2]
    change LeafNodeCacheProgram.rawOne p.headEnd.stacks=_
    simp only [LeafNodeCacheProgram.rawOne,h128,h207]

theorem Preparation.empty_word {s : HeadInputs} {a d : Data} (p : Preparation s a d)
    (ha : Ready s a) (i : Fin 768) (hi : i∈Node.cleanupPorts)
    (hl : i∉LayoutMasters.lowPorts) (hc : i∉LeafNodeCacheProgram.cachePorts)
    (he : i∉([78,163,169,710,711,712] : List (Fin 768))) : d.stacks i=[] := by
  have hn169 : i≠169 := fun h=>he (by simp [h])
  rw [p.support_frame _ hn169,p.cached_words,LeafNodeCacheProgram.cache_frame _ _ hc]
  change p.headEnd.stacks i=[]
  by_cases hw : 340 ≤ i.val ∧ i.val < 628
  · let j : Fin 288 := ⟨i.val-340,by omega⟩
    have hj : workPort (by decide) j=i := by apply Fin.ext; dsimp [workPort,j]; omega
    exact hj ▸ p.head.work_clean j
  by_cases hp : 640 ≤ i.val ∧ i.val < 680
  · exact p.head.private_clean i hp
  have hx : External i := by
    have hn163 : i≠163 := fun h=>he (by simp [h])
    have hn710 : i≠710 := fun h=>he (by simp [h])
    have hn711 : i≠711 := fun h=>he (by simp [h])
    have hn712 : i≠712 := fun h=>he (by simp [h])
    exact ⟨by omega,hn163,hn710,hn711,hn712⟩
  rw [p.head.frame _ hx,p.loaded_words]
  exact (LayoutMasters.loaded_frame (LayoutMasters.project a) i hl).trans
    (ha.blank i hi (fun h=>he (by simp [h])))

theorem Preparation.loaded_word {s : HeadInputs} {a d : Data} (p : Preparation s a d)
    (i : Fin 14) : d.stacks (LayoutMasters.low i)=(loadedState a).stacks (LayoutMasters.low i) := by
  have hval : (LayoutMasters.low i).val=128+i.val := rfl
  have hib := i.isLt
  have hn : LayoutMasters.low i≠169 := by intro h; have := congrArg Fin.val h; simp at this; omega
  have hc : LayoutMasters.low i∉LeafNodeCacheProgram.cachePorts := by
    intro h
    simp only [LeafNodeCacheProgram.cachePorts,List.mem_cons,List.mem_nil_iff,or_false] at h
    rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
      have := congrArg Fin.val h <;> simp only [Fin.coe_ofNat_eq_mod] at this <;> omega
  have hx : External (LayoutMasters.low i) := by
    refine ⟨Or.inl (by omega),?_,?_,?_,?_⟩ <;> intro h <;>
      have := congrArg Fin.val h <;> simp only [Fin.coe_ofNat_eq_mod] at this <;> omega
  rw [p.support_frame _ hn,p.cached_words,LeafNodeCacheProgram.cache_frame _ _ hc]
  exact (p.head.frame _ hx).trans (congrFun p.loaded_words _)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeNative

end

end OAI.Algorithms
