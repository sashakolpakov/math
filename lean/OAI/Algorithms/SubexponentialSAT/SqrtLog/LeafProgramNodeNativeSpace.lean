import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeLocalBounds

namespace OAI.Algorithms

/-! Every node scratch word is bounded without inspecting collector buffers. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeNative
open SubexponentialSAT BitProgram StructuredCalls LeafHeadSetupProgram
open SubexponentialSAT.SubexpSetupStorage MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem Preparation.after_head {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (i : Fin 768) (hi : i≠169) (hc : i∉LeafNodeCacheProgram.cachePorts) :
    b.stacks i=pr.headEnd.stacks i := by
  rw [pr.support_frame i hi,pr.cached_words,LeafNodeCacheProgram.cache_frame _ _ hc]
  rfl

theorem Preparation.retained_cache {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : Ready s a) :
    b.stacks 710=pr.head.words.flatten ∧
    b.stacks 711=List.replicate (s.R*s.width.length) false ∧ b.stacks 712=s.power.1 := by
  have hblank (i : Fin 768) (hc : i∈Node.cleanupPorts) (hg : 142 ≤ i.val) (hn : i≠78) :
      (loadedState a).stacks i=[] :=
    (LayoutMasters.loaded_frame (LayoutMasters.project a) i (not_low_of_ge hg)).trans (ha.blank i hc hn)
  have hcache (i : Fin 768) (hi : 710 ≤ i.val) : i ∉ LeafNodeCacheProgram.cachePorts := by
    intro h
    simp [LeafNodeCacheProgram.cachePorts] at h
    omega
  have hcleanup (i : Fin 768) (hlo : 710 ≤ i.val) (hhi : i.val < 713) :
      i ∈ Node.cleanupPorts :=
    (Node.mem_cleanup i).mpr (Or.inr (Or.inr (Or.inr ⟨hlo, hhi⟩)))
  constructor
  · rw [pr.after_head 710 (by norm_num) (hcache 710 (by norm_num)),pr.head.positive,
      pr.loaded_words,hblank 710 (hcleanup 710 (by norm_num) (by norm_num))
        (by norm_num) (by norm_num),List.append_nil]
  constructor
  · rw [pr.after_head 711 (by norm_num) (hcache 711 (by norm_num)),pr.head.negative,
      pr.loaded_words,hblank 711 (hcleanup 711 (by norm_num) (by norm_num))
        (by norm_num) (by norm_num),List.append_nil]
  · rw [pr.after_head 712 (by norm_num) (hcache 712 (by norm_num)),pr.head.denominator,
      pr.loaded_words,hblank 712 (hcleanup 712 (by norm_num) (by norm_num))
        (by norm_num) (by norm_num),List.append_nil]

def spaceBudget (s : HeadInputs) (B H J : ℕ) : ℕ :=
  B+(4*B+6)+s.R*s.width.length+(s.R+1)+H+SupportProgram.count s.n J*(2*s.n+1)

theorem Preparation.workspace_bound {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : Ready s a) (B H J : ℕ) (hb : LocalWordBound B a)
    (h243 : a.stacks 243=List.replicate J true)
    (hstream : (bucketsInput pr.bucketInputs).length ≤ H) :
    ∀ i∈Node.cleanupPorts,(b.stacks i).length ≤ spaceBudget s B H J := by
  have hl := loaded_localWordBound ha B hb
  have hdir (q : Fin 768 × Fin 768) (hq : q∈LeafNodeCacheProgram.directCopies) :
      (b.stacks q.2).length ≤ B := by
    rw [pr.direct_word ha q hq]
    apply hl
    simp only [LeafNodeCacheProgram.directCopies,List.mem_cons,List.mem_nil_iff,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hone : (LeafNodeCacheProgram.rawOne (loadedState a).stacks).length ≤ 4*B+6 := by
    have h128 := hl 128 (by decide)
    have h207 := hl 207 (by decide)
    have he := LeafNodeCacheProgram.rawOne_length (LeafNodeCacheProgram.project (loadedState a))
    change (LeafNodeCacheProgram.rawOne (loadedState a).stacks).length=
      2*((loadedState a).stacks 128).length+2*((loadedState a).stacks 207).length+6 at he
    omega
  have hwordslength : pr.head.words.flatten.length=s.R*s.width.length := by
    rw [cacheWords_flat_length pr.head.words s.width.length pr.head.cache.2.1,pr.head.cache.1]
    simp [unary]
  have h710 : (b.stacks 710).length=s.R*s.width.length := by
    rw [(pr.retained_cache ha).1,hwordslength]
  have h711 : (b.stacks 711).length=s.R*s.width.length := by
    simp [(pr.retained_cache ha).2.1]
  have h712 : (b.stacks 712).length ≤ s.R+1 := by
    rw [(pr.retained_cache ha).2.2]
    simp only [Native.Inputs.power,LayoutProgram.IntegerCache.denominatorWord,
      List.length_append,List.length_replicate,List.length_singleton]
    omega
  have h169 : (b.stacks 169).length=SupportProgram.count s.n J*(2*s.n+1) := by
    rw [pr.support_words,LeafSupportInputProgram.supportFrames_length,(pr.support_cap J h243).2]
  have h163 : (b.stacks 163).length ≤ H := by
    simpa only [Preparation.bucketInputs,pr.buckets] using hstream
  intro i hi
  by_cases hc : i∈LeafNodeCacheProgram.cachePorts
  · have hc' := hc
    simp only [LeafNodeCacheProgram.cachePorts,List.mem_cons,List.mem_nil_iff,or_false] at hc'
    rcases hc' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact (hdir (194,5) (by decide)).trans (by dsimp [spaceBudget]; omega)
      | exact (hdir (202,12) (by decide)).trans (by dsimp [spaceBudget]; omega)
      | exact (hdir (203,17) (by decide)).trans (by dsimp [spaceBudget]; omega)
      | exact (hdir (201,22) (by decide)).trans (by dsimp [spaceBudget]; omega)
      | exact (hdir (204,39) (by decide)).trans (by dsimp [spaceBudget]; omega)
      | exact (hdir (212,45) (by decide)).trans (by dsimp [spaceBudget]; omega)
      | exact (hdir (243,46) (by decide)).trans (by dsimp [spaceBudget]; omega)
      | exact (hdir (211,76) (by decide)).trans (by dsimp [spaceBudget]; omega)
      | exact (hdir (281,143) (by decide)).trans (by dsimp [spaceBudget]; omega)
      | exact (hdir (128,88) (by decide)).trans (by dsimp [spaceBudget]; omega)
      | exact (hdir (280,190) (by decide)).trans (by dsimp [spaceBudget]; omega)
      | exact (hdir (128,191) (by decide)).trans (by dsimp [spaceBudget]; omega)
      | (rw [(pr.one_word ha).1]; exact hone.trans (by dsimp [spaceBudget]; omega))
      | (rw [(pr.one_word ha).2]; exact hone.trans (by dsimp [spaceBudget]; omega))
  by_cases hlo : i∈LayoutMasters.lowPorts
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hlo
    rw [pr.loaded_word j]
    have hn : LayoutMasters.low j∉carriedPorts := by
      intro hx
      simp only [carriedPorts,List.mem_cons,List.mem_nil_iff,or_false] at hx
      rcases hx with hx|hx|hx|hx|hx|hx|hx <;>
        have hv := congrArg Fin.val hx <;>
        change 128+j.val=_ at hv <;> norm_num at hv <;> have := j.isLt <;> omega
    exact (hl _ hn).trans (by dsimp [spaceBudget]; omega)
  by_cases he : i∈([78,163,169,710,711,712] : List (Fin 768))
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl
    · have hx : b.stacks 78=a.stacks 78 := by
        rw [pr.after_head 78 (by decide) (by decide),pr.head.frame 78 (by norm_num [External,Fin.ext_iff]),
          pr.loaded_words]
        exact LayoutMasters.loaded_frame (LayoutMasters.project a) 78 (by decide)
      rw [hx]
      exact (hb 78 (by decide)).trans (by dsimp [spaceBudget]; omega)
    · exact h163.trans (by dsimp [spaceBudget]; omega)
    · rw [h169]; dsimp [spaceBudget]; omega
    · rw [h710]; dsimp [spaceBudget]; omega
    · rw [h711]; dsimp [spaceBudget]; omega
    · exact h712.trans (by dsimp [spaceBudget]; omega)
  · rw [pr.empty_word ha i hi hlo hc he]
    exact Nat.zero_le _

end SubexponentialSAT.SqrtLog.LeafProgram.NodeNative

end

end OAI.Algorithms
